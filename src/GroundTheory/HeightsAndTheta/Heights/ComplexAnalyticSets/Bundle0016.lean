module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthCutGlobal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped Pointwise

universe u v

namespace LengthCutGlobal

section Layers

variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]

theorem length_localized_add {N M Q : Type*} [AddCommGroup N] [Module C N] [AddCommGroup M]
    [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl N) +
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl Q) := by
  let fN := LocalizedModule.mkLinearMap P.primeCompl N
  let fM := LocalizedModule.mkLinearMap P.primeCompl M
  let fQ := LocalizedModule.mkLinearMap P.primeCompl Q
  exact Module.length_eq_add_of_exact
    ((IsLocalizedModule.map P.primeCompl fN fM f).extendScalarsOfIsLocalization P.primeCompl
      (Localization.AtPrime P))
    ((IsLocalizedModule.map P.primeCompl fM fQ g).extendScalarsOfIsLocalization P.primeCompl
      (Localization.AtPrime P))
    (IsLocalizedModule.map_injective P.primeCompl fN fM f hf)
    (IsLocalizedModule.map_surjective P.primeCompl fM fQ g hg)
    (IsLocalizedModule.map_exact P.primeCompl fN fM fQ f g H)


omit [P.IsPrime] in
theorem length_quotSMulTop_add (y : C) {N M Q : Type*} [AddCommGroup N] [Module C N]
    [AddCommGroup M] [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (hy : ∀ q : Q, y • q = 0 → q = 0) :
    Module.length C (QuotSMulTop y M) =
      Module.length C (QuotSMulTop y N) + Module.length C (QuotSMulTop y Q) := by
  refine Module.length_eq_add_of_exact (QuotSMulTop.map y f) (QuotSMulTop.map y g) ?_
    (QuotSMulTop.map_surjective y hg) (QuotSMulTop.map_exact y H hg)
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨m, -, hm⟩ := hx
  have hgm : g m = 0 := hy _ (by rw [← map_smul, hm]; exact (H (f n)).2 ⟨n, rfl⟩)
  obtain ⟨n', rfl⟩ := (H m).1 hgm
  have hn : n = y • n' := hf (by rw [map_smul, hm])
  rw [Submodule.Quotient.mk_eq_zero, hn]
  exact Submodule.smul_mem_pointwise_smul n' y ⊤ trivial

theorem lengths_of_subsingleton (y : C) (X : Type*) [AddCommGroup X] [Module C X] [Subsingleton X] :
    Module.length C (QuotSMulTop y X) = 0 ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = 0 := by
  have : Subsingleton (QuotSMulTop y X) := (Submodule.mkQ_surjective _).subsingleton
  exact ⟨Module.length_eq_zero, Module.length_eq_zero⟩

theorem smul_injective_pi {y : C} (hy : y ∉ P) (n : ℕ) (v : Fin n → C ⧸ P) (h : y • v = 0) :
    v = 0 := by
  funext i
  have hi := congrFun h i
  rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Pi.zero_apply] at hi
  exact (mul_eq_zero.1 hi).resolve_left (fun h => hy (Ideal.Quotient.eq_zero_iff_mem.1 h))


omit [P.IsPrime] in
theorem length_quotSMulTop_quot {y : C} (hmax : (P ⊔ Ideal.span {y}).IsMaximal) :
    Module.length C (QuotSMulTop y (C ⧸ P)) = 1 := by
  let g : C →ₗ[C] QuotSMulTop y (C ⧸ P) :=
    (y • (⊤ : Submodule C (C ⧸ P))).mkQ ∘ₗ Algebra.linearMap C (C ⧸ P)
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp Ideal.Quotient.mk_surjective
  have hker : LinearMap.ker g = P ⊔ Ideal.span {y} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Algebra.linearMap_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective t
      have hmem : x - y * c ∈ P := by
        rw [← Ideal.Quotient.eq, map_mul, ← Ideal.Quotient.algebraMap_eq, ← ht, Algebra.smul_def]
        rfl
      rw [show x = (x - y * c) + y * c by ring]
      exact Submodule.add_mem_sup hmem (Ideal.mem_span_singleton'.2 ⟨c, mul_comm c y⟩)
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine ⟨Ideal.Quotient.mk P c, ?_⟩
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add (f := _),
        Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, map_mul, mul_comm]
  rw [← (g.quotKerEquivOfSurjective hg).length_eq, hker]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.1 hmax))

theorem length_localized_quot :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (C ⧸ P)) = 1 := by
  let S := Localization.AtPrime P
  have hJ : (P : Submodule C C).localized' S P.primeCompl (Algebra.linearMap C S) =
      IsLocalRing.maximalIdeal S := by
    rw [Submodule.localized'_eq_span, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv P.primeCompl
    ((P : Submodule C C).toLocalizedQuotient' S P.primeCompl (Algebra.linearMap C S))
    (LocalizedModule.mkLinearMap P.primeCompl (C ⧸ P))).extendScalarsOfIsLocalization P.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.mpr
    (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal S)))

theorem lengths_pi {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) (n : ℕ) :
    Module.length C (QuotSMulTop y (Fin n → C ⧸ P)) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (Fin n → C ⧸ P)) = n := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero]
    exact lengths_of_subsingleton P y (Fin 0 → C ⧸ P)
  | succ n ih =>
    let f : (C ⧸ P) →ₗ[C] (Fin (n + 1) → C ⧸ P) := LinearMap.single C (fun _ => C ⧸ P) 0
    let g : (Fin (n + 1) → C ⧸ P) →ₗ[C] (Fin n → C ⧸ P) := LinearMap.funLeft C (C ⧸ P) Fin.succ
    have hf : Function.Injective f := fun a b h => by simpa [f] using congrFun h 0
    have hg : Function.Surjective g :=
      LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
    have H : Function.Exact f g := by
      intro v
      constructor
      · intro hv
        refine ⟨v 0, funext fun i => ?_⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [f]
        · have hj : v j.succ = 0 := congrFun hv j
          simp [f, hj, Fin.succ_ne_zero]
      · rintro ⟨t, rfl⟩
        funext j
        simp [f, g, LinearMap.funLeft, Fin.succ_ne_zero]
    rw [length_quotSMulTop_add y f g hf hg H (smul_injective_pi P hy n),
      length_localized_add P f g hf hg H, ih.1, ih.2, length_quotSMulTop_quot P hmax,
      length_localized_quot P]
    constructor <;> push_cast <;> ring

theorem lengths_free {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) {n : ℕ}
    {X : Type*} [AddCommGroup X] [Module C X] (e : X ≃ₗ[C] (Fin n → C ⧸ P)) :
    Module.length C (QuotSMulTop y X) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = n := by
  rw [(QuotSMulTop.congr y e).length_eq,
    (IsLocalizedModule.mapEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl X)
      (LocalizedModule.mkLinearMap P.primeCompl (Fin n → C ⧸ P)) (Localization.AtPrime P) e).length_eq]
  exact lengths_pi P hy hmax n

end Layers

theorem lengths_eq {C : Type u} [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (hPID : IsPrincipalIdealRing (C ⧸ P)) (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal)
    (k : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
      (∀ p ∈ P ^ k, ∀ m : M, p • m = 0) → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (QuotSMulTop y M) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) := by
  induction k with
  | zero =>
    intro M _ _ _ hann _
    have : Subsingleton M := ⟨fun a b => by
      rw [← one_smul C a, ← one_smul C b, hann 1 (by simp) a, hann 1 (by simp) b]⟩
    rw [(lengths_of_subsingleton P y M).1, (lengths_of_subsingleton P y M).2]
  | succ k ih =>
    intro M _ _ _ hann hinj
    have := hPID

    have : Module.Finite C (Submodule.torsionBySet C M (P : Set C)) :=
      Module.Finite.of_injective (Submodule.torsionBySet C M (P : Set C)).subtype
        (Submodule.torsionBySet C M (P : Set C)).injective_subtype
    have : Module.Finite (C ⧸ P) (Submodule.torsionBySet C M (P : Set C)) :=
      Module.Finite.of_restrictScalars_finite C (C ⧸ P) _
    have : Module.IsTorsionFree (C ⧸ P) (Submodule.torsionBySet C M (P : Set C)) := by
      refine Module.IsTorsionFree.of_smul_eq_zero fun r n h => ?_
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
      by_cases hs : s ∈ P
      · exact Or.inl (Ideal.Quotient.eq_zero_iff_mem.2 hs)
      · right
        rw [Submodule.torsionBySet.mk_smul] at h
        exact Subtype.ext (hinj s hs n (congrArg Subtype.val h))
    obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := C ⧸ P)
      (M := Submodule.torsionBySet C M (P : Set C))
    have hN := lengths_free P hy hmax (b.equivFun.restrictScalars C)

    have hannQ : ∀ p ∈ P ^ k, ∀ q : M ⧸ Submodule.torsionBySet C M (P : Set C), p • q = 0 := by
      intro p hp q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      rw [smul_smul]
      exact hann _ (by rw [pow_succ']; exact Ideal.mul_mem_mul ha hp) m
    have hinjQ : ∀ s ∉ P, ∀ q : M ⧸ Submodule.torsionBySet C M (P : Set C), s • q = 0 → q = 0 := by
      intro s hs q hq
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_torsionBySet_iff] at hq
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      apply hinj s hs
      rw [smul_comm]
      exact hq ⟨a, ha⟩
    have hQ := ih (M ⧸ Submodule.torsionBySet C M (P : Set C)) hannQ hinjQ
    let N := Submodule.torsionBySet C M (P : Set C)
    rw [length_quotSMulTop_add y N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N) (hinjQ y hy),
      length_localized_add P N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hQ, hN.1, hN.2]

theorem proof : LengthCutGlobal.Statement.{u, v} := by
  intro C _ _ P _ y M _ _ _ hnil hPID hy hmax hinj
  obtain ⟨k, hk⟩ := hnil
  rw [Submodule.ideal_span_singleton_smul]
  refine lengths_eq P y hPID hy hmax k M (fun p hp m => ?_) hinj
  rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
  rw [hp, zero_smul]

end LengthCutGlobal

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthLocalizedLocalized
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

theorem LengthLocalizedLocalized.isLocalization_atPrime_map (B : Type u) [CommRing B] (P Q : Ideal B)
    [hP : P.IsPrime] [Q.IsPrime] [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime] (hPQ : P ≤ Q) :
    IsLocalization P.primeCompl (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) := by
  have h : Ideal.under B (P.map (algebraMap B (Localization.AtPrime Q))) = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) hP
      (Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP))
  have key : IsLocalization ((P.map (algebraMap B (Localization.AtPrime Q))).comap
        (algebraMap B (Localization.AtPrime Q))).primeCompl
      (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime Q.primeCompl _
  rw [Ideal.under] at h
  have e : P.primeCompl = ((P.map (algebraMap B (Localization.AtPrime Q))).comap
      (algebraMap B (Localization.AtPrime Q))).primeCompl :=
    Submonoid.ext fun x => by rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, h]
  rw [e]
  exact key

theorem LengthLocalizedLocalized.proof : LengthLocalizedLocalized.Statement.{u, v} := by
  intro B _ P Q _ _ _ M _ _ hPQ
  have hloc := LengthLocalizedLocalized.isLocalization_atPrime_map B P Q hPQ

  let σ : Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))) ≃ₐ[B]
      Localization.AtPrime P := IsLocalization.algEquiv P.primeCompl _ _
  let : Algebra (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) := σ.toRingHom.toAlgebra
  let : Module (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    Module.compHom _ (algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P))
  have : IsScalarTower (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    ⟨fun r l x => by
      show (r • l) • x = algebraMap _ (Localization.AtPrime P) r • (l • x)
      rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower B (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    ⟨fun b r x => by
      show algebraMap _ (Localization.AtPrime P) (b • r) • x =
        b • (algebraMap _ (Localization.AtPrime P) r • x)
      rw [Algebra.smul_def, map_mul, mul_smul]
      rw [show algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (Localization.AtPrime P) (algebraMap B _ b) = algebraMap B (Localization.AtPrime P) b from
          σ.commutes b, algebraMap_smul]⟩

  have hf : IsBaseChange (Localization.AtPrime Q) (LocalizedModule.mkLinearMap Q.primeCompl M) :=
    IsLocalizedModule.isBaseChange Q.primeCompl _ _
  have hg : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
        (LocalizedModule Q.primeCompl M)) :=
    IsLocalizedModule.isBaseChange (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl _ _
  have hfg := hf.comp hg
  have h0 : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap P.primeCompl M) :=
    IsLocalizedModule.isBaseChange P.primeCompl _ _
  rw [← (h0.equiv.symm.trans hfg.equiv).length_eq]
  exact Module.length_eq_of_surjective σ.surjective

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalizationAtPrimeQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem LocalizationAtPrimeQuotient.proof : LocalizationAtPrimeQuotient.Statement.{u} := by
  intro A _ I T P _ W _ hP
  let Q := A ⧸ I
  let B := Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))

  have hsub : (P.comap (algebraMap Q (Localization T))).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    have hmem : ∀ r : A, Ideal.Quotient.mk I r ∈ P.comap (algebraMap Q (Localization T)) ↔ r ∈ W := by
      intro r; rw [← hP]; exact Iff.rfl
    have hIW : I ≤ W := fun r hr => by
      rw [← hmem, Ideal.Quotient.eq_zero_iff_mem.2 hr]; exact Ideal.zero_mem _
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q (Localization T))).primeCompl ↔ r ∉ W :=
      not_congr (hmem r)
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl) (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T
      (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) B
  refine ⟨e.toRingEquiv, fun a => ?_⟩
  have h2 : algebraMap (Localization T) (Localization.AtPrime P)
      (algebraMap Q (Localization T) (Ideal.Quotient.mk I a)) =
      algebraMap Q (Localization.AtPrime P) (Ideal.Quotient.mk I a) :=
    (IsScalarTower.algebraMap_apply Q (Localization T) (Localization.AtPrime P) _).symm
  rw [h2]
  exact e.commutes (Ideal.Quotient.mk I a)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalizeQuotientStages
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem length_self_eq_of_ringEquiv {A C : Type*} [CommRing A] [CommRing C] (e : A ≃+* C) :
    Module.length A A = Module.length C C := by
  have : RingHomSurjective (e : A →+* C) := ⟨e.surjective⟩
  let f : A →ₛₗ[(e : A →+* C)] C :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a b => by simp }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

theorem LocalizeQuotientStages.proof : LocalizeQuotientStages.Statement.{u} := by
  intro R _ m W I _ _ hWm hIW P _ hP
  let Q := R ⧸ I
  let B := Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))
  let T := Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))

  have hdisj : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have hPR : P.comap (algebraMap R B) = W := by
    rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime m) B, ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, ← hP,
      ← Ideal.map_map, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 (Ideal.map_mono hIW)]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ ‹W.IsPrime› hdisj

  have hsub : (P.comap (algebraMap Q B)).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q B)).primeCompl ↔ r ∉ W := by
      rw [← hPR]; exact Iff.rfl
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hBP : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl)
      (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid Q m.primeCompl) (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) T
  exact (length_self_eq_of_ringEquiv (A := Localization.AtPrime P) (C := T) e.toRingEquiv).trans
    (Module.length_eq_of_surjective (R := T) (S := Localization.AtPrime W) (M := T)
      Ideal.Quotient.mk_surjective).symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPowerSumsEsymmAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Finset

theorem multiset_mul_esymm_eq_sum (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map fun x => x ^ a.2).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun x : s => (x : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum s ℂ k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, MvPolynomial.psum,
    MvPolynomial.aeval_X] at h
  convert h using 4 with a _
  rw [Finset.sum_eq_multiset_sum]
  conv_lhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl

theorem PowerSumsEsymmAnalytic.proof : PowerSumsEsymmAnalytic.Statement := by
  intro σ _ V d Z hV hcard hp k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa [Multiset.esymm, Multiset.powersetCard_zero_left] using
      (analyticOnNhd_const (𝕜 := ℂ) (v := (1 : ℂ)) (s := V))
  by_cases hkd : d < k
  · refine (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ))).congr hV fun z hz => ?_
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard z hz]; exact hkd)]
  push Not at hkd
  have hsum : AnalyticOnNhd ℂ (fun z => ((k : ℂ))⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (Z z).esymm a.1 * ((Z z).map fun x => x ^ a.2).sum)) V := by
    refine analyticOnNhd_const.mul (analyticOnNhd_const.mul ?_)
    refine Finset.analyticOnNhd_fun_sum _ fun a ha => ?_
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    refine (analyticOnNhd_const.mul (ih a.1 ha.2)).mul (hp a.2 (by omega) (by omega))
  refine hsum.congr hV fun z _ => ?_
  rw [← multiset_mul_esymm_eq_sum, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), one_mul]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchContainsNormalPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def BranchContainsNormalPoint.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (k : ℕ) (r : ℝ) (φ : (Fin k → ℂ) → σ → ℂ) (B : Set (σ → ℂ)),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (zeroSetIn I) → B ∈ 𝓝 w →
    (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.ball 0 r → w ∈ φ '' Metric.ball 0 r

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

