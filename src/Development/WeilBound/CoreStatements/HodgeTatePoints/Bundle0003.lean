module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHensA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatDesc
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

theorem ext_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  intro R _ T _ R' _ φ A g
  let S : Submonoid (T → R') :=
    { carrier := {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)}
      one_mem' := ⟨1, one_mem A, funext fun t => by simp⟩
      mul_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨f', hf', rfl⟩
        exact ⟨f * f', mul_mem hf hf', funext fun t => by simp⟩ }
  have h := Algebra.adjoin_eq_span R' (S : Set (T → R'))
  rw [Submonoid.closure_eq] at h
  exact (Subalgebra.mem_toSubmodule _).symm.trans (h ▸ Iff.rfl)

theorem mem_descent : ∀ (R : Type) [CommRing R] (ι : Type) [Finite ι] (N : Submodule R (ι → R)) (f : ι → R), (∀ P : Ideal R, P.IsMaximal → ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R'), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ (fun i => algebraMap R R' (f i)) ∈ Submodule.span R' {g : ι → R' | ∃ n ∈ N, g = fun i => algebraMap R R' (n i)}) → f ∈ N := by
  intro R _ ι _ N f h
  classical
  let _ := Fintype.ofFinite ι
  let q : (ι → R) ⧸ N := N.mkQ f
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R _ q)
  by_contra hf
  have hI : I ≠ ⊤ := fun hI => hf (by
    have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : R) • q = 0 := h1
    rw [one_smul] at h2
    exact (Submodule.Quotient.mk_eq_zero N).1 h2)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨R', _, _, _, hflat, hc, hmem⟩ := h P hP
  let ψ : (ι → R') →ₗ[R'] R' ⊗[R] ((ι → R) ⧸ N) :=
    (N.mkQ.baseChange R') ∘ₗ (TensorProduct.piScalarRight R R' R' ι).symm.toLinearMap
  have hψ : ∀ n : ι → R, ψ (fun i => algebraMap R R' (n i)) = 1 ⊗ₜ N.mkQ n := fun n => by
    have : (TensorProduct.piScalarRight R R' R' ι).symm (fun i => algebraMap R R' (n i)) = 1 ⊗ₜ n := by
      rw [LinearEquiv.symm_apply_eq]
      funext i
      simp [Algebra.algebraMap_eq_smul_one]
    show (N.mkQ.baseChange R') ((TensorProduct.piScalarRight R R' R' ι).symm _) = _
    rw [this, LinearMap.baseChange_tmul]
  have h0 : (1 : R') ⊗ₜ[R] q = 0 := by
    rw [← hψ]
    refine (Submodule.span_le (p := LinearMap.ker ψ)).2 ?_ hmem
    rintro _ ⟨n, hn, rfl⟩
    show ψ _ = 0
    rw [hψ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 hn, tmul_zero]
  let g : (R ⧸ I) →ₗ[R] ((ι → R) ⧸ N) := I.liftQ (LinearMap.toSpanSingleton R _ q) le_rfl
  have hg : Function.Injective g := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  have h1 : (1 : R') ⊗ₜ[R] (Submodule.Quotient.mk 1 : R ⧸ I) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := R') g hg
    rw [LinearMap.lTensor_tmul, map_zero, ← h0]
    congr 1
    exact one_smul R q
  let k := R' ⧸ IsLocalRing.maximalIdeal R'
  let a : (R ⧸ I) →ₗ[R] k := I.liftQ (Algebra.linearMap R k) fun r hr => by
    have : r ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') := hc ▸ hle hr
    exact Ideal.Quotient.eq_zero_iff_mem.2 this
  have h2 := congrArg (LinearMap.mul' R k ∘ₗ
    TensorProduct.map (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal R')).toLinearMap a) h1
  rw [map_zero, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply] at h2
  have h3 : a (Submodule.Quotient.mk 1) = 1 := map_one (algebraMap R k)
  rw [h3, mul_one] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R').ne_top
    ((Ideal.eq_top_iff_one _).2 (Ideal.Quotient.eq_zero_iff_mem.1 h2))

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHens
section
namespace PositivityTheory.HtPt.Htat.Hens

open CategoryTheory Polynomial IsLocalRing TensorProduct

section PiLocalization₂

variable {R : Type} [CommRing R] [IsDomain R] {S : Type} [CommRing S] [Algebra R S] [Algebra.Etale R S]

theorem stage_inj : Function.Injective (algebraMap S (S ⊗[R] FractionRing R)) :=
  Algebra.TensorProduct.includeLeft_injective (S := R) (IsFractionRing.injective R (FractionRing R))

theorem stage_int [IsIntegrallyClosed R] {z : S ⊗[R] FractionRing R} (hz : IsIntegral S z) :
    ∃ s, algebraMap S _ s = z := by
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S)
    (B := FractionRing R)).2 ⟨z, hz⟩
  have ht' : Algebra.TensorProduct.map (AlgHom.id S S) (integralClosure R (FractionRing R)).val t = z :=
    congrArg Subtype.val ht
  rw [← ht']
  clear ht ht'
  induction t with
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | tmul x y =>
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := R) y.2
    refine ⟨r • x, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]

omit [Algebra.Etale R S] in
theorem stage_den (z : S ⊗[R] FractionRing R) :
    ∃ (r : R) (y : S), r ≠ 0 ∧ algebraMap S _ y = algebraMap S _ (algebraMap R S r) * z := by
  induction z with
  | add x y hx hy =>
    obtain ⟨r, a, hr, ha⟩ := hx
    obtain ⟨s, b, hs, hb⟩ := hy
    refine ⟨r * s, algebraMap R S s * a + algebraMap R S r * b, mul_ne_zero hr hs, ?_⟩
    simp only [map_add (f := _), map_mul, ha, hb]
    ring
  | tmul x y =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) y
    have hb' := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FractionRing R) hb
    refine ⟨b, a • x, nonZeroDivisors.ne_zero hb, ?_⟩
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [← Algebra.smul_def, smul_tmul, smul_tmul, Algebra.smul_def, Algebra.smul_def, mul_one,
      mul_div_cancel₀ _ hb']

theorem stage_reg (x : S ⊗[R] FractionRing R) : ∃ z, x * x * z = x := by
  let F := FractionRing R
  have : Module.Finite F (F ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free F _
  have : IsReduced (F ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field F _
  have : IsArtinianRing (F ⊗[R] S) := IsArtinianRing.of_finite F _
  let e := (Algebra.TensorProduct.comm R S F).toRingEquiv.trans (IsArtinianRing.equivPi (F ⊗[R] S)).toRingEquiv
  have key : ∀ y : (∀ m : MaximalSpectrum (F ⊗[R] S), (F ⊗[R] S) ⧸ m.asIdeal), ∃ w, y * y * w = y := fun y => by
    have : ∀ m, ∃ w, y m * y m * w = y m := fun m => by
      let _ := Ideal.Quotient.field m.asIdeal
      by_cases h : y m = 0
      · exact ⟨0, by simp [h]⟩
      · exact ⟨(y m)⁻¹, by rw [mul_assoc, mul_inv_cancel₀ h, mul_one]⟩
    choose w hw using this
    exact ⟨w, funext hw⟩
  obtain ⟨w, hw⟩ := key (e x)
  exact ⟨e.symm w, e.injective (by rw [map_mul, map_mul, e.apply_symm_apply, hw])⟩

theorem stage_idem [IsIntegrallyClosed R] (x : S) :
    ∃ (e y : S) (r : R), e * e = e ∧ e * x = x ∧ r ≠ 0 ∧ x * y = algebraMap R S r * e := by
  obtain ⟨z, hz⟩ := stage_reg (R := R) (algebraMap S (S ⊗[R] FractionRing R) x)
  have hi : IsIntegral S (algebraMap S (S ⊗[R] FractionRing R) x * z) :=
    ⟨X ^ 2 - X, monic_X_pow_sub (degree_X_le.trans_lt (by norm_num)), by
      simp only [eval₂_sub, eval₂_X_pow, eval₂_X]
      linear_combination z * hz⟩
  obtain ⟨e, he⟩ := stage_int hi
  obtain ⟨r, y, hr, hy⟩ := stage_den z
  refine ⟨e, y, r, stage_inj (R := R) ?_, stage_inj (R := R) ?_, hr, stage_inj (R := R) ?_⟩
  · rw [map_mul, he]; linear_combination z * hz
  · rw [map_mul, he]; linear_combination hz
  · rw [map_mul, map_mul, he, hy]; ring

end PiLocalization₂

namespace etaleColimit

open PointedEtale

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

theorem flat : Module.Flat R (etaleColimit R K) := by
  classical
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} h => ?_
  obtain ⟨X, hX⟩ := exists_of_finset (Finset.univ.image x)
  choose x' hx' using fun i => hX (x i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have h0 : of X (∑ i, f i • x' i) = of X 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, ← h, ← ofAlgHom_apply, map_sum]
    simp only [map_smul, ofAlgHom_apply, hx']
  obtain ⟨Y, g, hg⟩ := exists_hom_eq_of_of_eq h0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at hg
  simp only [map_smul] at hg
  obtain ⟨k, a, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := Y) (f := f)
    (x := fun i => g.alg (x' i)) hg
  refine ⟨k, a, fun j => of Y (y j), fun i => ?_, h2⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hx', ← of_map g, show g.alg (x' i) = _ from h1 i, ← ofAlgHom_apply, map_sum]
  simp only [map_smul, ofAlgHom_apply]

variable [IsDomain R]

theorem reg {r : R} (hr : r ≠ 0) {a : etaleColimit R K} (h : algebraMap R _ r * a = 0) : a = 0 := by
  have := flat (R := R) (K := K)
  have hreg : IsSMulRegular (etaleColimit R K) r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
  exact hreg (show r • a = r • 0 by rw [smul_zero, Algebra.smul_def, h])

variable [IsIntegrallyClosed R]

theorem exists_dvd {a : etaleColimit R K} (ha : a ≠ 0) : ∃ (b : etaleColimit R K) (r : R), r ≠ 0 ∧
    a * b = algebraMap R _ r := by
  obtain ⟨X, x, rfl⟩ := exists_of a
  obtain ⟨e, y, r, h1, h2, hr, h3⟩ := stage_idem (R := R) x
  have he : of X e * (1 - of X e) = 0 := by rw [mul_sub, ← map_mul, h1, mul_one, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (of X e) with hu | hu
  · have : of X e = 1 := (sub_eq_zero.1 (hu.mul_right_eq_zero.1 he)).symm
    exact ⟨of X y, r, hr, by rw [← map_mul, h3, map_mul, this, mul_one, of_algebraMap]⟩
  · exact absurd (by rw [← h2, map_mul, hu.mul_left_eq_zero.1 he, zero_mul]) ha

theorem isDomain : IsDomain (etaleColimit R K) := by
  have : NoZeroDivisors (etaleColimit R K) := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · obtain ⟨c, r, hr, hc⟩ := exists_dvd ha
      exact Or.inr (reg hr (by rw [← hc]; linear_combination c * h))⟩
  exact NoZeroDivisors.to_isDomain _

theorem dvd_of_root {r : R} (hr : r ≠ 0) {h : etaleColimit R K} {p : (etaleColimit R K)[X]} (hp : p.Monic)
    (hz : (p.scaleRoots (algebraMap R _ r)).eval h = 0) : ∃ y, h = algebraMap R _ r * y := by
  obtain ⟨X₁, q₁, hq₁, rfl⟩ := exists_monic_lift p hp
  obtain ⟨X₂, x₂, rfl⟩ := exists_of h
  let X := tensor X₁ X₂
  let q : X.carrier[X] := q₁.map (inl X₁ X₂).alg.toRingHom
  have hq : q.Monic := hq₁.map _
  let x : X := (inr X₁ X₂).alg x₂
  have e1 : q.map (of X) = q₁.map (of X₁) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun a => of_map (inl X₁ X₂) a
  have e2 : of X x = of X₂ x₂ := of_map _ _
  have sc : ∀ {A B : Type} [CommRing A] [CommRing B] [Nontrivial B] (φ : A →+* B) (q : A[X]) (_ : q.Monic) (s a : A),
      φ ((q.scaleRoots s).eval a) = ((q.map φ).scaleRoots (φ s)).eval (φ a) := fun φ q hq s a => by
    rw [← map_scaleRoots _ _ _ (by rw [hq.leadingCoeff, map_one]; exact one_ne_zero), Polynomial.eval_map, eval₂_at_apply]
  have h0 : of X ((q.scaleRoots (algebraMap R X r)).eval x) = of X 0 := by
    rw [sc _ _ hq, e1, e2, of_algebraMap, hz, map_zero]
  obtain ⟨Y, g, hg⟩ := exists_hom_eq_of_of_eq h0
  have : Nontrivial Y := (of Y).domain_nontrivial
  have : Nontrivial (Y ⊗[R] FractionRing R) := (stage_inj (R := R) (S := Y)).nontrivial
  rw [map_zero] at hg
  let ι := algebraMap Y (Y ⊗[R] FractionRing R)
  let t : Y ⊗[R] FractionRing R := 1 ⊗ₜ (algebraMap R (FractionRing R) r)⁻¹
  have hrt : ι (algebraMap R Y r) * t = 1 := by
    have hr' : algebraMap R (FractionRing R) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr
    simp only [ι, t, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul, Algebra.smul_def, mul_inv_cancel₀ hr']
    rfl
  let q' : Y.carrier[X] := q.map g.alg.toRingHom
  have hq' : q'.Monic := hq.map _
  have h1 : (q'.scaleRoots (algebraMap R Y r)).eval (g.alg x) = 0 := by
    have := sc g.alg.toRingHom q hq (algebraMap R X r) x
    rw [show g.alg.toRingHom (algebraMap R X r) = algebraMap R Y r from g.alg.commutes r] at this
    exact this.symm.trans hg
  have hi : IsIntegral Y (ι (g.alg x) * t) := by
    refine ⟨q', hq', ?_⟩
    have h2 := scaleRoots_eval₂_mul (p := q') ι (ι (g.alg x) * t) (algebraMap R Y r)
    rw [show ι (algebraMap R Y r) * (ι (g.alg x) * t) = ι (g.alg x) by linear_combination ι (g.alg x) * hrt,
      eval₂_at_apply, h1, map_zero] at h2
    exact ((IsUnit.of_mul_eq_one _ hrt).pow _).mul_right_eq_zero.1 h2.symm
  obtain ⟨y, hy⟩ := stage_int hi
  have h3 : g.alg x = algebraMap R Y r * y := stage_inj (R := R) (by
    rw [map_mul, hy]
    show ι _ = ι _ * _
    linear_combination (-ι (g.alg x)) * hrt)
  exact ⟨of Y y, by rw [← e2, ← of_map g, h3, map_mul, of_algebraMap]⟩

theorem isIntegrallyClosed : IsIntegrallyClosed (etaleColimit R K) := by
  have := isDomain (R := R) (K := K)
  let H := etaleColimit R K
  refine (isIntegrallyClosed_iff (FractionRing H)).2 fun {z} hz => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := H) z
  obtain ⟨c, r, hr, hc⟩ := exists_dvd (nonZeroDivisors.ne_zero hb)
  obtain ⟨p, hp, hz⟩ := hz
  have hinj := IsFractionRing.injective H (FractionRing H)
  have hb' := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FractionRing H) hb
  have e : algebraMap H (FractionRing H) (algebraMap R H r) *
      (algebraMap H (FractionRing H) a / algebraMap H (FractionRing H) b) = algebraMap H _ (a * c) := by
    rw [← hc, map_mul, map_mul, mul_right_comm, mul_div_cancel₀ _ hb']
  have h2 := scaleRoots_eval₂_eq_zero (algebraMap H (FractionRing H)) (s := algebraMap R H r) hz
  rw [e, eval₂_at_apply, map_eq_zero_iff _ hinj] at h2
  obtain ⟨y, hy⟩ := dvd_of_root hr hp h2
  refine ⟨y, ?_⟩
  have hr0 : algebraMap H (FractionRing H) (algebraMap R H r) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 fun h => one_ne_zero (reg hr (a := (1 : H)) (by rw [h, zero_mul]))
  exact mul_left_cancel₀ hr0 (by rw [e, hy, map_mul])

end etaleColimit

end PositivityTheory.HtPt.Htat.Hens

namespace PositivityTheory.HtPt.Htat

open Hens in
theorem hens_normal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : HenselianLocalRing R') (_ : Algebra R R'), IsIntegrallyClosed R' ∧ Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P := by
  intro R _ _ _ P _
  have hs : Function.Surjective (etaleColimit.toK : etaleColimit R P.ResidueField →+* P.ResidueField) := by
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ P) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := P.ResidueField) hb
    have hk : ∀ c : R, algebraMap (R ⧸ P) P.ResidueField (Ideal.Quotient.mk P c) =
        etaleColimit.toK (algebraMap R (etaleColimit R P.ResidueField) c) := fun c => by
      rw [etaleColimit.toK_algebraMap]; rfl
    rw [hk] at hb'
    obtain ⟨t, ht⟩ := (etaleColimit.isUnit_of_toK_ne_zero hb').exists_right_inv
    refine ⟨algebraMap R _ a * t, ?_⟩
    have := congrArg etaleColimit.toK ht
    rw [map_mul, map_one] at this
    rw [hk, hk, map_mul, div_eq_mul_inv, eq_inv_of_mul_eq_one_right this]
  refine ⟨etaleColimit R P.ResidueField, inferInstance, etaleColimit.isDomain, etaleColimit.henselianLocalRing hs,
    inferInstance, etaleColimit.isIntegrallyClosed, etaleColimit.flat, ?_⟩
  ext r
  refine Iff.trans ?_ (Ideal.algebraMap_residueField_eq_zero (I := P) (x := r))
  rw [← etaleColimit.toK_algebraMap, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    etaleColimit.isUnit_iff_toK_ne_zero, not_not]

end PositivityTheory.HtPt.Htat
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ProjectiveUnramifiedQuotient
section
namespace PositivityTheory.HtPt.Mi

theorem algHom_of_system : ∀ (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A] (I : Ideal R) [IsAdicComplete I R] (f : ∀ e : ℕ, B →ₐ[R] A ⧸ (I ^ (e + 1)).map (algebraMap R A)), (∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b) → ∃! g : B →ₐ[R] A, ∀ e b, Ideal.Quotient.mk _ (g b) = f e b := by
  intro R A B _ _ _ _ _ _ _ I _ f hf
  have := GlobalTheory.isAdicComplete_map_of_finite I A
  let J := I.map (algebraMap R A)
  have hJ : ∀ e, (I ^ e).map (algebraMap R A) = J ^ e := fun e => Ideal.map_pow _ _ _
  have ha : StrictMono fun e : ℕ => e + 1 := fun _ _ h => Nat.succ_lt_succ h
  let f' : ∀ e : ℕ, B →+* A ⧸ J ^ (e + 1) := fun e => (Ideal.quotEquivOfEq (hJ (e + 1))).toRingHom.comp (f e).toRingHom
  have key : ∀ e (a : A) (b : B), Ideal.Quotient.mk _ a = f' e b ↔ Ideal.Quotient.mk _ a = f e b := fun e a b => by
    rw [← (Ideal.quotEquivOfEq (hJ (e + 1))).injective.eq_iff, Ideal.quotEquivOfEq_mk]
    rfl
  have hf' : ∀ {m}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp (f' (m + 1)) = f' m := fun {m} => by
    ext b
    obtain ⟨a, hb⟩ := Ideal.Quotient.mk_surjective (f' (m + 1) b)
    rw [RingHom.comp_apply, ← hb, ← (key m a b).2 (hf m b a ((key _ a b).1 hb))]
    rfl
  let g := IsAdicComplete.StrictMono.liftRingHom J ha f' hf'
  have hg : ∀ e b, Ideal.Quotient.mk _ (g b) = f' e b := fun e b =>
    IsAdicComplete.StrictMono.mk_liftRingHom J ha f' hf' b
  have ext : ∀ a a' : A, (∀ e, Ideal.Quotient.mk (J ^ (e + 1)) a = Ideal.Quotient.mk (J ^ (e + 1)) a') → a = a' :=
    fun a a' h => congrFun (IsHausdorff.StrictMono.funext' J ha (f := fun _ : Unit => a) (g := fun _ => a')
      fun e _ => h e) ()
  refine ⟨{ g with commutes' := fun r => ext _ _ fun e => ?_ }, fun e b => (key e _ b).1 (hg e b),
    fun g' hg' => AlgHom.ext fun b => ext _ _ fun e => ?_⟩
  · refine (hg e _).trans ((key e _ _).2 ?_).symm
    rw [AlgHom.commutes]; rfl
  · exact ((key e _ b).2 (hg' e b)).trans (hg e b).symm

end PositivityTheory.HtPt.Mi
end

