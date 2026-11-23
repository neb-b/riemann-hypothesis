module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureAdjoinUnitBallCoeffBound
section
open Polynomial

namespace GlobalTheory

theorem closure_adjoin_unitBall_coeff_bound : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (ζ : PadicAlgCl l), IsIntegral ℚ_[l] ζ → ∃ (n : ℕ) (C : ℝ), ∀ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))), ‖x‖ ≤ 1 → ∃ c : Fin n → ℂ_[l], (∀ i, c i ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖c i‖ ≤ C) ∧ x = ∑ i, c i * (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (i : ℕ) := by
  intro l _ F ζ hζ
  set ι := algebraMap (PadicAlgCl l) ℂ_[l] with hι
  let F0 : Subfield ℂ_[l] := (F.toSubfield.map ι).topologicalClosure
  have hF0 : (F0 : Set ℂ_[l]) = closure (ι '' (F : Set (PadicAlgCl l))) := rfl
  have hmemF : ∀ y ∈ F, ι y ∈ F0 := fun y hy =>
    Subfield.le_topologicalClosure _ ⟨y, hy, rfl⟩
  obtain ⟨r, hr⟩ := NontriviallyNormedField.non_trivial (α := ℚ_[l])
  have hrmem : ι (algebraMap ℚ_[l] (PadicAlgCl l) r) ∈ F0 := hmemF _ (F.algebraMap_mem r)
  have hrnorm : ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖ = ‖r‖ := by
    rw [← PadicComplex.coe_eq, PadicComplex.norm_extends]
    exact PadicAlgCl.norm_extends l r
  letI : NontriviallyNormedField F0 :=
    { SubfieldClass.toNormedField F0 with
      non_trivial := ⟨⟨_, hrmem⟩, by
        show 1 < ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖
        rw [hrnorm]; exact hr⟩ }
  haveI : CompleteSpace F0 := (Subfield.isClosed_topologicalClosure _).completeSpace_coe
  letI : NormedSpace F0 ℂ_[l] :=
    { norm_smul_le := fun a b => by
        show ‖(a : ℂ_[l]) * b‖ ≤ ‖(a : ℂ_[l])‖ * ‖b‖
        exact (norm_mul _ _).le }
  set z := ι ζ with hz
  set q := minpoly ℚ_[l] ζ with hq
  set n := q.natDegree with hn
  let g : ℚ_[l] →+* F0 := (ι.comp (algebraMap ℚ_[l] (PadicAlgCl l))).codRestrict F0
    (fun r => hmemF _ (F.algebraMap_mem r))
  let Q : F0[X] := q.map g
  have hQmonic : Q.Monic := (minpoly.monic hζ).map g
  have hQdeg : Q.natDegree = n := (minpoly.monic hζ).natDegree_map g
  have hQroot : aeval z Q = 0 := by
    have h1 : (algebraMap F0 ℂ_[l]).comp g = ι.comp (algebraMap ℚ_[l] (PadicAlgCl l)) := by
      ext; rfl
    rw [aeval_def, eval₂_map, h1, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hQ1 : Q ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hQdeg, natDegree_one] at this
    exact (minpoly.natDegree_pos hζ).ne' this
  let φ : (Fin n → F0) →ₗ[F0] ℂ_[l] := Fintype.linearCombination F0 (fun i : Fin n => z ^ (i : ℕ))
  have hpoly : ∀ p : F0[X], aeval z p ∈ LinearMap.range φ := by
    intro p
    rw [← aeval_modByMonic_eq_self_of_root (p := p) hQroot]
    have hd : (p %ₘ Q).natDegree < n := hQdeg ▸ natDegree_modByMonic_lt p hQmonic hQ1
    rw [aeval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range (fun i => (p %ₘ Q).coeff i • z ^ i)]
    exact ⟨fun i => (p %ₘ Q).coeff i, by rw [Fintype.linearCombination_apply]⟩
  have hadj : ∀ y ∈ Algebra.adjoin F0 {z}, y ∈ LinearMap.range φ := by
    intro y hy
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    exact hpoly p
  let B : Subalgebra ℚ_[l] (PadicAlgCl l) :=
    { (Algebra.adjoin F0 {z}).toSubsemiring.comap ι with
      algebraMap_mem' := fun r => by
        show ι (algebraMap ℚ_[l] _ r) ∈ Algebra.adjoin F0 {z}
        exact (Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF _ (F.algebraMap_mem r)⟩ : F0) }
  have hsub : ∀ y ∈ (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)),
      ι y ∈ Algebra.adjoin F0 {z} := by
    intro y hy
    have hle : (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ}).toSubalgebra ≤ B := by
      rw [IntermediateField.sup_toSubalgebra_of_isAlgebraic_right]
      refine sup_le ?_ ?_
      · intro w hw
        exact (Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF w hw⟩ : F0)
      · rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ.isAlgebraic]
        refine Algebra.adjoin_le (Set.singleton_subset_iff.2 ?_)
        exact Algebra.subset_adjoin rfl
    exact hle hy
  have hclosed : IsClosed ((LinearMap.range φ : Submodule F0 ℂ_[l]) : Set ℂ_[l]) :=
    Submodule.closed_of_finiteDimensional _
  have hcl : closure (ι '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} :
      IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))) ⊆ LinearMap.range φ :=
    closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact hadj _ (hsub y hy)) hclosed
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker φ)
  have hψker : LinearMap.ker (φ.domRestrict W) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun w hw => ?_
    exact Subtype.ext (Submodule.disjoint_def.1 hW.disjoint _ hw w.2)
  obtain ⟨C0, -, hC0⟩ := (φ.domRestrict W).exists_antilipschitzWith hψker
  refine ⟨n, C0, fun x hx hx1 => ?_⟩
  obtain ⟨v, hv⟩ := hcl hx
  obtain ⟨k, hk, w, hw, hkw⟩ := Submodule.mem_sup.1 (hW.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hφw : φ w = x := by
    rw [← hv, ← hkw, map_add (f := _), LinearMap.mem_ker.1 hk, zero_add]
  have hwn : ‖w‖ ≤ C0 := by
    have h := hC0.le_mul_dist ⟨w, hw⟩ 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h
    have h2 : ‖(φ.domRestrict W) ⟨w, hw⟩‖ = ‖x‖ := by
      rw [LinearMap.domRestrict_apply, hφw]
    rw [h2] at h
    calc ‖w‖ = ‖(⟨w, hw⟩ : W)‖ := rfl
      _ ≤ C0 * ‖x‖ := h
      _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left hx1 C0.2
      _ = C0 := mul_one _
  refine ⟨fun i => (w i : ℂ_[l]), fun i => ⟨(w i).2, ?_⟩, ?_⟩
  · exact (norm_le_pi_norm w i).trans hwn
  · rw [← hφw, Fintype.linearCombination_apply]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapSingleSpanAlgebraMapNumberField
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

theorem exists_integral_dual_family (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] :
    ∃ (k : ℕ) (b : Fin k → 𝓞 M) (l : Fin k → M →ₗ[E] E),
      (∀ j (c : 𝓞 M), ∃ a : 𝓞 E, l j (c : M) = (a : E)) ∧
      ∀ y : M, y = ∑ j, (b j : M) * algebraMap E M (l j y) := by
  haveI : Module.Finite (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.Flat (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.FinitePresentation (𝓞 E) (𝓞 M) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (𝓞 M) := Module.Flat.projective_of_finitePresentation
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) (𝓞 M)
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  haveI hL : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 M) (nonZeroDivisors (𝓞 E))) M :=
    IsIntegralClosure.isLocalization (𝓞 E) E M (𝓞 M)
  haveI hL' : IsLocalizedModule (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hL
  have hu : ∀ x : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) x
  let l0 : Fin k → M →ₗ[𝓞 E] E := fun j =>
    IsLocalizedModule.lift (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu
  let l : Fin k → M →ₗ[E] E := fun j =>
    (l0 j).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E
  have hl : ∀ j (c : 𝓞 M), l j (c : M) = ((σ c j : 𝓞 E) : E) := by
    intro j c
    exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu c
  refine ⟨k, fun j => π (Pi.single j 1), l, fun j c => ⟨_, hl j c⟩, ?_⟩
  have hc : ∀ c : 𝓞 M, (c : M) = ∑ j, ((π (Pi.single j 1) : 𝓞 M) : M) * algebraMap E M (l j c) := by
    intro c
    have h1 : c = ∑ j, σ c j • π (Pi.single j 1) := by
      have h2 : π (σ c) = c := LinearMap.congr_fun hσ c
      conv_lhs => rw [← h2, LinearMap.pi_apply_eq_sum_univ π (σ c)]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ext i
      simp [Pi.single_apply, eq_comm]
    have h3 := congrArg (algebraMap (𝓞 M) M) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h3
    refine h3.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [hl, Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply]
    rfl
  intro y
  obtain ⟨⟨c, a⟩, ha⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap y
  have ha' : ((a : 𝓞 E) : E) • y = (c : M) := by
    have : (a : 𝓞 E) • y = (c : M) := ha
    rw [← this]
    exact algebraMap_smul E (a : 𝓞 E) y
  have hne : ((a : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero a.2
    exact_mod_cast this
  have h4 := hc c
  rw [← ha'] at h4
  apply smul_right_injective M hne
  dsimp only
  rw [h4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
  ring

theorem comap_single_span_algebraMap (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι) :
    (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap
      (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) =
    Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap
      (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by
  apply le_antisymm
  · obtain ⟨k, b, l, hl, hy⟩ := exists_integral_dual_family E M
    have key : ∀ j, ∀ w ∈ Submodule.span (𝓞 M)
        ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S), ∀ c : 𝓞 M,
        (fun i => l j ((c : M) * w i)) ∈ Submodule.span (𝓞 E) S := by
      intro j w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        intro c
        obtain ⟨a, ha⟩ := hl j c
        have : (fun i => l j ((c : M) * algebraMap E M (v i))) = a • v := by
          ext i
          rw [mul_comm, ← Algebra.smul_def, map_smul, ha, smul_eq_mul, mul_comm]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
      | zero =>
        intro c
        have : (fun i => l j ((c : M) * (0 : ι → M) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        intro c
        have : (fun i => l j ((c : M) * (x + y) i)) =
            (fun i => l j ((c : M) * x i)) + (fun i => l j ((c : M) * y i)) := by
          ext i; simp [mul_add]
        rw [this]; exact Submodule.add_mem _ (hx c) (hy c)
      | smul a x _ hx =>
        intro c
        have : (fun i => l j ((c : M) * (a • x) i)) =
            (fun i => l j (((c * a : 𝓞 M) : M) * x i)) := by
          ext i
          congr 1
          rw [Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
          simp
        rw [this]; exact hx _
    intro s hs
    rw [hy s]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 : ((b j : 𝓞 M) : M) * algebraMap E M (l j s) = b j • algebraMap E M (l j s) := rfl
    rw [h1]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨l j s, ?_, rfl⟩)
    have h2 := key j _ hs 1
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have key : ∀ v ∈ Submodule.span (𝓞 E) S, (fun i => algebraMap E M (v i)) ∈
        Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have : (fun i => algebraMap E M ((0 : ι → E) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have : (fun i => algebraMap E M ((x + y) i)) =
            (fun i => algebraMap E M (x i)) + (fun i => algebraMap E M (y i)) := by
          ext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        have : (fun i => algebraMap E M ((a • x) i)) =
            algebraMap (𝓞 E) (𝓞 M) a • (fun i => algebraMap E M (x i)) := by
          ext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
            ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have h2 := key _ hs
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorProdFst
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem conductor_prod_fst (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S]
    (e : S ≃+* R × S') (d : S)
    (hd : ∀ c : FractionRing S, IsIntegral S c →
      ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) :
    ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  intro c hc
  let g : S →+* FractionRing R × FractionRing S' :=
    (RingHom.prodMap (algebraMap R (FractionRing R)) (algebraMap S' (FractionRing S'))).comp
      e.toRingHom
  have hgx : ∀ x : S, g x = (algebraMap R (FractionRing R) (e x).1,
      algebraMap S' (FractionRing S') (e x).2) := fun x => rfl
  have hg : ∀ y : nonZeroDivisors S, IsUnit (g y) := by
    intro y
    rw [hgx, Prod.isUnit_iff]
    have h1 : (e y).1 ∈ nonZeroDivisors R := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (z, 0) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).1) this
      simpa using this
    have h2 : (e y).2 ∈ nonZeroDivisors S' := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (0, z) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).2) this
      simpa using this
    exact ⟨IsLocalization.map_units (FractionRing R) (⟨_, h1⟩ : nonZeroDivisors R),
      IsLocalization.map_units (FractionRing S') (⟨_, h2⟩ : nonZeroDivisors S')⟩
  let Θ : FractionRing S →+* FractionRing R × FractionRing S' := IsLocalization.lift hg
  have hΘ : ∀ x : S, Θ (algebraMap S (FractionRing S) x) = g x := fun x =>
    IsLocalization.lift_eq hg x
  have hΘinj : Function.Injective Θ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h; rw [(IsFractionRing.injective S (FractionRing S)) h]
    · intro h
      have h' : e x = e y := by
        rw [hgx, hgx] at h
        ext
        · exact IsFractionRing.injective R (FractionRing R) (congrArg Prod.fst h)
        · exact IsFractionRing.injective S' (FractionRing S') (congrArg Prod.snd h)
      rw [e.injective h']

  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
  have hb' : e.symm ((b : R), (1 : S')) ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    have hz' := congrArg e hz
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero] at hz'
    have h1 : (e z).1 * b = 0 := congrArg Prod.fst hz'
    have h2 : (e z).2 * 1 = 0 := congrArg Prod.snd hz'
    rw [mul_right_mem_nonZeroDivisors_eq_zero_iff b.2] at h1
    rw [mul_one] at h2
    apply e.injective
    rw [map_zero]
    ext <;> simp [h1, h2]
  set c := IsLocalization.mk' (FractionRing R) a b with hcdef
  let b' : nonZeroDivisors S := ⟨_, hb'⟩
  let c' : FractionRing S := IsLocalization.mk' (FractionRing S) (e.symm (a, 0)) b'
  have hΘc : Θ c' = (c, 0) := by
    have hs := IsLocalization.mk'_spec (FractionRing S) (e.symm (a, 0)) b'
    have hs2 := congrArg Θ hs
    rw [map_mul, hΘ, hΘ] at hs2
    have hu := hg b'
    have hcs := IsLocalization.mk'_spec (FractionRing R) a b
    rw [← hu.mul_left_inj, hs2]
    rw [hgx, hgx]
    simp only [b', RingEquiv.apply_symm_apply, Prod.mk_mul_mk, map_zero, map_one, mul_one,
      zero_mul]
    rw [hcs]
  have hf : Function.Surjective ((RingHom.fst R S').comp e.toRingHom) := by
    intro r
    exact ⟨e.symm (r, 0), by simp⟩
  have hc' : IsIntegral S c' := by
    obtain ⟨p, hpm, hp⟩ := hc
    obtain ⟨q, hqmap, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
      (f := (RingHom.fst R S').comp e.toRingHom) (p := p)
      ((lifts_iff_coeff_lifts p).mpr (fun n => hf _)) hpm
    refine ⟨X * q, monic_X.mul hqm, ?_⟩
    apply hΘinj
    rw [Polynomial.hom_eval₂, map_zero, hΘc, eval₂_mul, eval₂_X]
    have hfst : (RingHom.fst (FractionRing R) (FractionRing S')).comp
        (Θ.comp (algebraMap S (FractionRing S))) =
        (algebraMap R (FractionRing R)).comp ((RingHom.fst R S').comp e.toRingHom) := by
      ext x
      simp [hΘ, hgx]
    have h1 : (eval₂ (Θ.comp (algebraMap S (FractionRing S))) (c, 0) q).1 = 0 := by
      have := Polynomial.hom_eval₂ q (Θ.comp (algebraMap S (FractionRing S)))
        (RingHom.fst (FractionRing R) (FractionRing S')) (c, 0)
      simp only [RingHom.coe_fst] at this
      rw [this, hfst, ← eval₂_map, hqmap]
      exact hp
    ext
    · simp [h1]
    · simp
  obtain ⟨s, hs⟩ := hd c' hc'
  refine ⟨(e s).1, ?_⟩
  have h := congrArg (fun z => (Θ z).1) hs
  simp only [map_mul, hΘ, hΘc, hgx, Prod.fst_mul] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory


open MeasureTheory Filter Topology in
open scoped ContDiff in
theorem _root_.GlobalTheory.contDiff_of_continuous_oneParameter (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (T : ℝ → A) (hT : Continuous T) (h0 : T 0 = 1)
    (hadd : ∀ s t, T (s + t) = T s * T t) : ContDiff ℝ ∞ T := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → A, G = fun x => ∫ s in (0:ℝ)..x, T s := ⟨_, rfl⟩
  have hG : ∀ x, HasDerivAt G (T x) x := fun x => by
    rw [hGdef]; exact (hT.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hG0 : G 0 = 0 := by rw [hGdef]; exact intervalIntegral.integral_same
  have hlim : Tendsto (fun δ : ℝ => δ⁻¹ • G δ) (𝓝[≠] 0) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (hG 0)
    rw [h0] at h
    refine h.congr' (Eventually.of_forall fun δ => ?_)
    simp [slope_def_module, hG0]
  obtain ⟨δ, hδu, hδ0⟩ :=
    ((hlim.eventually (Units.isOpen.mem_nhds isUnit_one)).and self_mem_nhdsWithin).exists
  have hδ : δ ≠ 0 := hδ0
  have hu : IsUnit (G δ) := by
    have e : G δ = algebraMap ℝ A δ * (δ⁻¹ • G δ) := by
      rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ, one_smul]
    rw [e]
    exact ((Ne.isUnit hδ).map (algebraMap ℝ A)).mul hδu
  have key : ∀ t, T t * G δ = G (t + δ) - G t := by
    intro t
    have h1 := (ContinuousLinearMap.mul ℝ A (T t)).intervalIntegral_comp_comm
      (hT.intervalIntegrable (μ := volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [hGdef]
    dsimp only
    rw [← h1, intervalIntegral.integral_interval_sub_left (hT.intervalIntegrable (μ := volume) _ _)
      (hT.intervalIntegrable (μ := volume) _ _)]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun x => T x) t, add_zero]
  have hform : T = fun t => (G (t + δ) - G t) * ↑hu.unit⁻¹ := by
    funext t
    rw [← key, mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hT
  | succ n ih =>
    have hGn : ContDiff ℝ (n + 1 : ℕ) G := by
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun x => (hG x).differentiableAt, by simp, ?_⟩
      rwa [show deriv G = T from funext fun x => (hG x).deriv]
    rw [hform]
    exact ((hGn.comp (contDiff_id.add contDiff_const)).sub hGn).mul contDiff_const

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtDet
section
namespace GlobalTheory.DifferentiableDet

theorem differentiableAt_det {σ : Type} [Fintype σ] [DecidableEq σ] (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (h : ∀ (i j : σ), DifferentiableAt ℝ (fun (s : ℝ) ↦ M s i j) t) :
    DifferentiableAt ℝ (fun (s : ℝ) ↦ Matrix.det (M s)) t := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun π _ => ?_
  refine DifferentiableAt.const_mul ?_ _
  exact (HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s => M s (π i) i)
    (fun i _ => (h (π i) i).hasDerivAt)).differentiableAt

end GlobalTheory.DifferentiableDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastNotMemOfPrimeNe
section
namespace GlobalTheory.NatCastNotMemPrime

theorem natCast_notMem_of_prime_ne {A : Type} [inst : CommRing A] (P : Ideal A)
    [hP : Ideal.IsPrime P] {p l : ℕ} (hp : Nat.Prime p) (hl : Nat.Prime l) (hne : l ≠ p)
    (hpP : (↑p : A) ∈ P) : (↑l : A) ∉ P := by
  intro hlP
  have hcop : Nat.Coprime l p := (Nat.coprime_primes hl hp).2 hne
  have hc : IsCoprime (l : A) (p : A) := Nat.Coprime.cast hcop
  obtain ⟨a, b, hab⟩ := hc
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact P.add_mem (P.mul_mem_left a hlP) (P.mul_mem_left b hpP)

end GlobalTheory.NatCastNotMemPrime
end

