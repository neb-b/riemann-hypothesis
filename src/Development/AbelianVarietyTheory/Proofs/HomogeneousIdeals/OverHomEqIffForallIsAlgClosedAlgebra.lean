module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace GlobalTheory

section Ext

variable {T Y S : Scheme.{u}}

theorem hom_eq_iff_forall_field [IsReduced T] (s : Y ⟶ S) [IsSeparated s] {f g : T ⟶ Y}
    (h : f ≫ s = g ≫ s) :
    f = g ↔ ∀ (k : Type u) [Field k] (x : Spec (.of k) ⟶ T), x ≫ f = x ≫ g :=
  ⟨fun e _ _ _ => e ▸ rfl, fun H => ext_of_fromSpecResidueField_eq f g s Set.univ dense_univ
    (fun x _ => H (T.residueField x) (T.fromSpecResidueField x)) h⟩

theorem hom_eq_iff_forall_isAlgClosed [IsReduced T] (s : Y ⟶ S) [IsSeparated s] {f g : T ⟶ Y}
    (h : f ≫ s = g ≫ s) :
    f = g ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ T), x ≫ f = x ≫ g := by
  refine ⟨fun e _ _ _ _ => e ▸ rfl, fun H => (hom_eq_iff_forall_field s h).mpr fun k _ x => ?_⟩
  let ι : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : Surjective ι := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  refine ext_of_isDominant_of_isSeparated s (by simp only [Category.assoc, h]) ι ?_
  simpa only [Category.assoc] using H _ (ι ≫ x)

variable {R : Type u} [CommRing R]

theorem over_hom_eq_iff_forall_isAlgClosed_algebra {T Y : Over (Spec (.of R))} [IsReduced T.left]
    [IsSeparated Y.hom] {f g : T ⟶ Y} :
    f = g ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g := by
  refine ⟨fun e _ _ _ _ _ => e ▸ rfl, fun H => Over.OverMorphism.ext ?_⟩
  refine (hom_eq_iff_forall_isAlgClosed Y.hom ((Over.w f).trans (Over.w g).symm)).mpr
    fun k _ _ x => ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ T.hom)
  letI : Algebra R k := φ.hom.toAlgebra
  exact congrArg (·.left) (H k (Over.homMk x hφ.symm))

theorem over_hom_eq_iff_forall_field_algebra {T Y : Over (Spec (.of R))} [IsReduced T.left]
    [IsSeparated Y.hom] {f g : T ⟶ Y} :
    f = g ↔ ∀ (k : Type u) [Field k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g :=
  ⟨fun e _ _ _ _ => e ▸ rfl,
    fun H => over_hom_eq_iff_forall_isAlgClosed_algebra.mpr fun k _ _ _ x => H k x⟩

theorem eq_zero_of_forall_field {A : Type u} [CommRing A] [_root_.IsReduced A] {a : A}
    (h : ∀ (k : Type u) [Field k] (φ : A →+* k), φ a = 0) : a = 0 :=
  IsNilpotent.eq_zero (nilpotent_iff_mem_prime.mpr fun p _ =>
    Ideal.algebraMap_residueField_eq_zero.mp (h p.ResidueField (algebraMap A _)))

end Ext

namespace WeierstrassCurve

section Algebra

variable {A : Type*} [CommRing A]

theorem exists_unit_smul_of_minors {ι : Type*} [Fintype ι] {P Q : ι → A}
    (hP : Ideal.span (Set.range P) = ⊤) (hQ : Ideal.span (Set.range Q) = ⊤)
    (h : ∀ i j, P i * Q j = P j * Q i) : ∃ u : Aˣ, Q = (u : A) • P := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hP.ge (Submodule.mem_top (x := 1)))
  have e : Q = (∑ i, a i * Q i) • P := by
    ext j
    rw [Pi.smul_apply, smul_eq_mul, Finset.sum_mul, ← one_mul (Q j), ← ha, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by linear_combination a i * h i j
  have hu : IsUnit (∑ i, a i * Q i) := by
    rw [← Ideal.span_singleton_eq_top, _root_.eq_top_iff, ← hQ, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [congrFun e j]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  exact ⟨hu.unit, e⟩

theorem IsUnimodularSol.exists_isUnit [IsLocalRing A] {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : IsUnimodularSol V P) : ∃ i, IsUnit (P i) := by
  by_contra! H
  have : Ideal.span (Set.range P) ≤ IsLocalRing.maximalIdeal A := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact H i
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h.span_eq_top ▸ this))

theorem isUnimodularSol_iff_ne_zero {k : Type*} [Field k] {V : WeierstrassCurve k}
    {P : Fin 3 → k} : IsUnimodularSol V P ↔ V.toProjective.Equation P ∧ P ≠ 0 := by
  refine ⟨fun h => ⟨h.equation, ?_⟩, fun ⟨h, h0⟩ => ?_⟩
  · obtain ⟨i, hi⟩ := h.exists_isUnit
    rintro rfl
    exact hi.ne_zero rfl
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h0
    exact .of_isUnit h i (Ne.isUnit hi)

theorem IsUnimodularSol.of_nonsingular {k : Type*} [Field k] {V : WeierstrassCurve k}
    {P : Fin 3 → k} (h : V.toProjective.Nonsingular P) : IsUnimodularSol V P :=
  isUnimodularSol_iff_ne_zero.mpr ⟨h.left, AddLaw.ne_zero_of_nonsingular h⟩

theorem isUnimodularSol_iff_nonsingular {k : Type*} [Field k] {V : WeierstrassCurve k}
    [V.IsElliptic] {P : Fin 3 → k} : IsUnimodularSol V P ↔ V.toProjective.Nonsingular P :=
  isUnimodularSol_iff_ne_zero.trans
    (AddLaw.nonsingular_iff_of_Δ_ne_zero V.isUnit_Δ.ne_zero P).symm

theorem IsUnimodularSol.nonsingular {k : Type*} [Field k] {V : WeierstrassCurve k}
    [V.IsElliptic] {P : Fin 3 → k} (h : IsUnimodularSol V P) : V.toProjective.Nonsingular P :=
  isUnimodularSol_iff_nonsingular.mp h

theorem equation_of_forall_field {A : Type u} [CommRing A] [_root_.IsReduced A]
    {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : ∀ (k : Type u) [Field k] (φ : A →+* k), (V.map φ).toProjective.Equation (φ ∘ P)) :
    V.toProjective.Equation P := by
  refine eq_zero_of_forall_field fun k _ φ => ?_
  have := h k φ
  change (V.toProjective.map φ).Equation _ at this
  rwa [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
    MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp] at this

end Algebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Injective

variable {A : Type u} [CommRing A]

private theorem basicOpen_eq_top_iff (a : A) : PrimeSpectrum.basicOpen a = ⊤ ↔ IsUnit a := by
  rw [← Ideal.span_singleton_eq_top, ← PrimeSpectrum.iSup_basicOpen_eq_top_iff',
    iSup_singleton]

private theorem minors_of_isUnit {ρ : R →+* A} {P Q : Fin 3 → A}
    {hP : IsUnimodularSol (W.map ρ) P} {hQ : IsUnimodularSol (W.map ρ) Q}
    (e : ptHom W ρ P hP = ptHom W ρ Q hQ) {i : Fin 3} (hi : IsUnit (P i)) (j l : Fin 3) :
    P j * Q l = P l * Q j := by
  have hi' : IsUnit (Q i) := by
    have h₁ := ptHom_preimage_coordOpen W ρ P hP i
    rw [e, ptHom_preimage_coordOpen] at h₁
    exact (basicOpen_eq_top_iff _).mp (h₁.trans ((basicOpen_eq_top_iff _).mpr hi))
  rw [ptHom_eq_awayChart W i ρ P hP hi, ptHom_eq_awayChart W i ρ Q hQ hi', cancel_mono] at e
  have e' : awayEval W i ρ P hP.equation hi = awayEval W i ρ Q hQ.equation hi' :=
    congrArg (·.hom) (Spec.map_injective e)
  rw [← awayEval_awayCoord_mul W i ρ P hP.equation hi j,
    ← awayEval_awayCoord_mul W i ρ P hP.equation hi l,
    ← awayEval_awayCoord_mul W i ρ Q hQ.equation hi' j,
    ← awayEval_awayCoord_mul W i ρ Q hQ.equation hi' l, e']
  ring

theorem ptHom_eq_ptHom_iff_minors {ρ : R →+* A} {P Q : Fin 3 → A}
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q) :
    ptHom W ρ P hP = ptHom W ρ Q hQ ↔ ∀ j l, P j * Q l = P l * Q j := by
  refine ⟨fun e j l => ?_, fun h => ?_⟩
  · rw [← sub_eq_zero, ← Submodule.mem_bot A]
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range P) hP.span_eq_top _ ?_
    rintro ⟨_, i, rfl⟩
    let φ := algebraMap A (Localization.Away (P i))
    have e' : ptHom W (φ.comp ρ) (φ ∘ P) (hP.map_comp φ) =
        ptHom W (φ.comp ρ) (φ ∘ Q) (hQ.map_comp φ) := by
      rw [← SpecMap_ptHom W ρ P hP, ← SpecMap_ptHom W ρ Q hQ, e]
    have h := minors_of_isUnit W e' (i := i) (IsLocalization.Away.algebraMap_isUnit (P i)) j l
    have h0 : φ (P j * Q l - P l * Q j) = 0 := by
      rw [map_sub, map_mul, map_mul, sub_eq_zero]
      exact h
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (.powers (P i)) _ _).mp h0
    exact ⟨n, hn⟩
  · obtain ⟨v, rfl⟩ := exists_unit_smul_of_minors hP.span_eq_top hQ.span_eq_top h
    exact (ptHom_smul W ρ P hP v.isUnit).symm

theorem ptHom_eq_ptHom_iff {ρ : R →+* A} {P Q : Fin 3 → A}
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q) :
    ptHom W ρ P hP = ptHom W ρ Q hQ ↔ ∃ v : Aˣ, Q = (v : A) • P := by
  refine ⟨fun e => exists_unit_smul_of_minors hP.span_eq_top hQ.span_eq_top
    ((ptHom_eq_ptHom_iff_minors W hP hQ).mp e), ?_⟩
  rintro ⟨v, rfl⟩
  exact (ptHom_smul W ρ P hP v.isUnit).symm

variable [Algebra R A] {P Q : Fin 3 → A}

theorem pt_eq_pt_iff_minors (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    pt W P hP = pt W Q hQ ↔ ∀ j l, P j * Q l = P l * Q j :=
  ptHom_eq_ptHom_iff_minors W hP.of_baseChange hQ.of_baseChange

theorem pt_eq_pt_iff (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    pt W P hP = pt W Q hQ ↔ ∃ v : Aˣ, Q = (v : A) • P :=
  ptHom_eq_ptHom_iff W hP.of_baseChange hQ.of_baseChange

theorem ptOver_eq_ptOver_iff (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    ptOver W P hP = ptOver W Q hQ ↔ ∃ v : Aˣ, Q = (v : A) • P :=
  Iff.trans ⟨fun e => congrArg (·.left) e, fun e => Over.OverMorphism.ext e⟩
    (pt_eq_pt_iff W hP hQ)

end Injective

section Local

variable {A : Type u} [CommRing A]

theorem exists_eq_ptHom_of_preimage_eq_top (ρ : R →+* A) (f : Spec (.of A) ⟶ scheme W)
    (hf : f ≫ toSpec W = Spec.map (CommRingCat.ofHom ρ)) (i : Fin 3)
    (hi : f ⁻¹ᵁ coordOpen W i = ⊤) :
    ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), P i = 1 ∧ f = ptHom W ρ P h := by
  have hr : Set.range f ⊆ Set.range (awayChart W i) := by
    rintro _ ⟨x, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, opensRange_awayChart]
    exact hi.ge (Set.mem_univ x)
  obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift (awayChart W i) f hr)
  have e : f = ptHom W (g.hom.comp (awayConst W i)) (g.hom ∘ awayCoord W i)
      ((isUnimodularSol_awayCoord W i).map_comp g.hom) := by
    rw [← SpecMap_awayChart, CommRingCat.ofHom_hom, hg, IsOpenImmersion.lift_fac]
  have hρ : g.hom.comp (awayConst W i) = ρ := by
    rw [e, ptHom_toSpec] at hf
    exact congrArg (·.hom) (Spec.map_injective hf)
  subst hρ
  exact ⟨_, _, by simp, e⟩

theorem exists_eq_ptHom [IsLocalRing A] (ρ : R →+* A) (f : Spec (.of A) ⟶ scheme W)
    (hf : f ≫ toSpec W = Spec.map (CommRingCat.ofHom ρ)) :
    ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), f = ptHom W ρ P h := by
  have : ∃ i, f (IsLocalRing.closedPoint A) ∈ coordOpen W i := by
    rcases (coordOpen_one_sup_coordOpen_two W).ge
      (Set.mem_univ (f (IsLocalRing.closedPoint A))) with h | h
    exacts [⟨_, h⟩, ⟨_, h⟩]
  obtain ⟨i, hi⟩ := this
  obtain ⟨P, h, -, e⟩ := exists_eq_ptHom_of_preimage_eq_top W ρ f hf i
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) f hi)
  exact ⟨P, h, e⟩

variable [Algebra R A]

theorem exists_eq_pt [IsLocalRing A] (f : Spec (.of A) ⟶ scheme W)
    (hf : f ≫ toSpec W = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P), f = pt W P h :=
  exists_eq_ptHom W _ f hf

theorem exists_eq_ptOver [IsLocalRing A]
    (f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W) :
    ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P), f = ptOver W P h := by
  obtain ⟨P, h, e⟩ := exists_eq_pt W f.left (Over.w f)
  exact ⟨P, h, Over.OverMorphism.ext e⟩





end Local

section Field

instance isElliptic_baseChange [W.IsElliptic] (A : Type*) [CommRing A] [Algebra R A] :
    (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

def zeroOver (A : Type u) [CommRing A] [Algebra R A] :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ zero W)
    (by simp [zero_toSpec])

theorem zeroOver_eq_ptOver (A : Type u) [CommRing A] [Algebra R A] :
    zeroOver W A = ptOver W (A := A) ![0, 1, 0] (isUnimodularSol_zero _) :=
  Over.OverMorphism.ext (SpecMap_algebraMap_zero W A)

variable (k K : Type u) [Field k] [Field K] [Algebra R k] [Algebra R K]

def ofProjectivePoint (p : (W.baseChange k).toProjective.Point) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W :=
  Quotient.hrecOn p.point (motive := fun c => (W.baseChange k).toProjective.NonsingularLift c →
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W))
    (fun P h => ptOver W P (.of_nonsingular h))
    (fun P Q e => Function.hfunext
      (propext (WeierstrassCurve.Projective.nonsingular_of_equiv e)) fun hP hQ _ =>
        heq_of_eq ((ptOver_eq_ptOver_iff W (.of_nonsingular hQ) (.of_nonsingular hP)).mpr
          (e.imp fun _ e => e.symm)).symm)
    p.nonsingular


@[simp] theorem ofProjectivePoint_zero : ofProjectivePoint W k 0 = zeroOver W k :=
  (zeroOver_eq_ptOver W k).symm

theorem ofProjectivePoint_injective : Function.Injective (ofProjectivePoint W k) := by
  rintro @⟨⟨P⟩, hP⟩ @⟨⟨Q⟩, hQ⟩ e
  obtain ⟨v, hv⟩ := (ptOver_eq_ptOver_iff W (.of_nonsingular hQ) (.of_nonsingular hP)).mp e.symm
  exact WeierstrassCurve.Projective.Point.ext (Quotient.sound ⟨v, hv.symm⟩)

def ofAffinePoint (p : (W.baseChange k).toAffine.Point) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W :=
  ofProjectivePoint W k (WeierstrassCurve.Projective.Point.fromAffine p)

@[simp] theorem ofAffinePoint_zero : ofAffinePoint W k 0 = zeroOver W k :=
  ofProjectivePoint_zero W k


variable {k} in
@[simp] theorem ofAffinePoint_some {a b : k} (h : (W.baseChange k).toAffine.Nonsingular a b) :
    ofAffinePoint W k (.some a b h) = ptOver W ![a, b, 1] (isUnimodularSol_some h.left) := rfl






variable [(W.baseChange k).IsElliptic] [(W.baseChange K).IsElliptic]

theorem ofProjectivePoint_bijective : Function.Bijective (ofProjectivePoint W k) := by
  refine ⟨ofProjectivePoint_injective W k, fun f => ?_⟩
  obtain ⟨P, h, rfl⟩ := exists_eq_ptOver W f
  exact ⟨⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr h.nonsingular⟩, rfl⟩

theorem ofAffinePoint_bijective : Function.Bijective (ofAffinePoint W k) := by
  classical
  exact (ofProjectivePoint_bijective W k).comp
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.baseChange k).toProjective).symm.bijective

def projectivePointEquiv : (W.baseChange k).toProjective.Point ≃
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W) :=
  Equiv.ofBijective _ (ofProjectivePoint_bijective W k)

def affinePointEquiv : (W.baseChange k).toAffine.Point ≃
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W) :=
  Equiv.ofBijective _ (ofAffinePoint_bijective W k)


variable {k} in
theorem projectivePointEquiv_symm_ptOver (P : Fin 3 → k)
    (h : IsUnimodularSol (W.baseChange k) P) :
    (projectivePointEquiv W k).symm (ptOver W P h) =
      ⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr h.nonsingular⟩ :=
  (Equiv.symm_apply_eq _).mpr rfl



end Field

end WeierstrassCurve

end GlobalTheory
