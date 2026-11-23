module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Anisotropic

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.AnisotropicHolds
section
namespace PI.Witt

theorem anisotropic' : Anisotropic := by
  unfold Anisotropic
  intro K V _ _ _ _ _ B hB U hU
  obtain ⟨x, hx, y, hy, hxy⟩ := hU
  by_contra hcon
  push_neg at hcon
  have hz : x + star (B x y) • y ∈ U := U.add_mem hx (U.smul_mem _ hy)
  have h0 := hcon _ hz
  have hxx := hcon x hx
  have hyy := hcon _ (U.smul_mem (star (B x y)) hy)
  have hyx : B y x = star (B x y) := (hB x y).symm
  have e1 : B x (star (B x y) • y) = star (B x y) * B x y := by
    rw [LinearMap.map_smul, smul_eq_mul]
  have e2 : B (star (B x y) • y) x = B x y * star (B x y) := by
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star, hyx]
  have e3 : B (x + star (B x y) • y) (x + star (B x y) • y) =
      B x x + B x (star (B x y) • y) + (B (star (B x y) • y) x + B (star (B x y) • y) (star (B x y) • y)) := by
    rw [LinearMap.map_add₂, map_add (f := _), map_add (f := _)]
  rw [e3, hxx, hyy, e1, e2] at h0
  have h2 : (2 : K) * (B x y * star (B x y)) = 0 := by linear_combination h0
  rcases mul_eq_zero.mp h2 with h | h
  · exact two_ne_zero h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hxy h'
    · exact hxy (star_eq_zero.mp h')

end PI.Witt
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Imports
section
namespace PI.Witt

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem riesz [FiniteDimensional K V] (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (φ : V →ₗ[K] K) : ∃ v, ∀ z, B v z = φ z := by
  classical
  let b := Module.finBasis K V
  rcases isEmpty_or_nonempty (Fin (Module.finrank K V)) with hE | hNE
  · refine ⟨0, fun z => ?_⟩
    have hz : z = 0 := by rw [← b.sum_repr z]; simp
    simp [hz]
  have hli : LinearIndependent K (fun i => B (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : B (∑ j, star (g j) • b j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smulₛₗ, starRingEnd_apply, star_star]
      exact hg
    have h2 : ∑ j, star (g j) • b j = 0 := hnd _ (fun y => by rw [h1, LinearMap.zero_apply])
    have h3 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h2 i
    exact star_eq_zero.mp h3
  have hcard : Fintype.card (Fin (Module.finrank K V)) = Module.finrank K (V →ₗ[K] K) := by
    rw [Fintype.card_fin]; exact (Subspace.dual_finrank_eq).symm
  let b' := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨∑ i, star (b'.repr φ i) • b i, fun z => ?_⟩
  conv_rhs => rw [← b'.sum_repr φ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, LinearMap.smul_apply, starRingEnd_apply, star_star,
    coe_basisOfLinearIndependentOfCardEqFinrank]

end PI.Witt
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Nondeg
section
namespace PI.Witt

variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]

theorem nondeg_extend (h1 : OneVector) (h2 : Anisotropic) [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x) :
    ∀ (n : ℕ) (U : Submodule K V), Module.finrank K U = n →
      (∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0) →
      ∀ f : U →ₗ[K] V, (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ (∀ x : U, g x = f x) ∧
        ∀ z, (∀ u : U, B (u : V) z = 0) → (∀ u : U, B (f u) z = 0) → g z = z := by
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro U hU hnd f hf
  by_cases hex : ∃ x ∈ U, ∃ y ∈ U, B x y ≠ 0
  · obtain ⟨u, hu, hBu⟩ := h2 K V B hB U hex
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ :=
      h1 K V B hB u (f ⟨u, hu⟩) (hf ⟨u, hu⟩ ⟨u, hu⟩).symm hBu
    have hsym : ∀ a b, B (g₁.symm a) b = B a (g₁ b) := by
      intro a b
      rw [← hg₁ (g₁.symm a) b, LinearEquiv.apply_symm_apply]
    have hsym₂ : ∀ a b, B (g₁.symm a) (g₁.symm b) = B a b := by
      intro a b
      rw [hsym, LinearEquiv.apply_symm_apply]
    let U' : Submodule K V := U ⊓ LinearMap.ker (B u)
    have hle : U' ≤ U := inf_le_left
    have hker : ∀ w ∈ U', B u w = 0 := fun w hw => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2
    have hwu : ∀ w ∈ U', B w u = 0 := by
      intro w hw
      rw [← hB u w, hker w hw, star_zero]
    have hproj : ∀ y ∈ U, y - (B u y / B u u) • u ∈ U' := by
      intro y hy
      refine Submodule.mem_inf.mpr ⟨U.sub_mem hy (U.smul_mem _ hu), LinearMap.mem_ker.mpr ?_⟩
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hBu, sub_self]
    have hlt : Module.finrank K U' < n := by
      rw [← hU]
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle fun heq => hBu ?_)
      have hu' : u ∈ U' := by rw [heq]; exact hu
      exact hker u hu'
    have hnd' : ∀ x ∈ U', (∀ y ∈ U', B x y = 0) → x = 0 := by
      intro x hx hxy
      refine hnd x (hle hx) fun y hy => ?_
      have h := hxy _ (hproj y hy)
      rw [map_sub, map_smul, hwu x hx, smul_zero, sub_zero] at h
      exact h
    let f' : U' →ₗ[K] V := g₁.symm.toLinearMap ∘ₗ f ∘ₗ Submodule.inclusion hle
    have hf'x : ∀ x : U', f' x = g₁.symm (f (Submodule.inclusion hle x)) := fun x => rfl
    have hf' : ∀ x y : U', B (f' x) (f' y) = B x y := by
      intro x y
      rw [hf'x, hf'x, hsym₂, hf]
      rfl
    obtain ⟨g₂, hg₂, hg₂f, hg₂fix⟩ := ih _ hlt U' rfl hnd' f' hf'
    have hg₂u : g₂ u = u := by
      refine hg₂fix u (fun w => hwu w w.2) fun w => ?_
      rw [hf'x, hsym, hg₁u, hf]
      exact hwu w w.2
    refine ⟨g₂.trans g₁, fun x y => ?_, fun x => ?_, fun z hz₁ hz₂ => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      rw [hg₁, hg₂]
    · obtain ⟨c, hc⟩ : ∃ c : K, c = B u x / B u u := ⟨_, rfl⟩
      have hmem : (x : V) - c • u ∈ U' := hc ▸ hproj x x.2
      let x' : U' := ⟨_, hmem⟩
      have hxv : (x : V) = c • u + (x' : V) := by simp [x']
      have hxU : x = c • (⟨u, hu⟩ : U) + Submodule.inclusion hle x' := Subtype.ext (by simp [x'])
      calc (g₂.trans g₁) (x : V) = g₁ (g₂ (c • u + (x' : V))) := by rw [← hxv]; rfl
        _ = c • g₁ u + g₁ (f' x') := by
            rw [map_add (f := _), map_smul, hg₂u, hg₂f x', map_add (f := _), map_smul]
        _ = f x := by
            rw [hg₁u, hf'x, LinearEquiv.apply_symm_apply]
            conv_rhs => rw [hxU]
            rw [map_add (f := _), map_smul]
    · have hg₁z : g₁ z = z := hg₁fix z (hz₁ ⟨u, hu⟩) (hz₂ ⟨u, hu⟩)
      have hg₂z : g₂ z = z := by
        refine hg₂fix z (fun w => hz₁ (Submodule.inclusion hle w)) fun w => ?_
        rw [hf'x, hsym, hg₁z]
        exact hz₂ _
      show g₁ (g₂ z) = z
      rw [hg₂z, hg₁z]
  · push Not at hex
    refine ⟨LinearEquiv.refl K V, fun x y => rfl, fun x => ?_, fun z _ _ => rfl⟩
    have hx0 : x = 0 := Subtype.ext (hnd x x.2 (hex x x.2))
    subst hx0
    simp

end PI.Witt
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.OneVector
section
namespace PI.Witt

section
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
  (B : V →ₗ⋆[K] V →ₗ[K] K)

def qrefl (v : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - (a⁻¹ • (B v)).smulRight v

lemma qrefl_apply (v : V) (a : K) (z : V) : qrefl B v a z = z - (a⁻¹ * B v z) • v := by
  simp [qrefl, LinearMap.smulRight_apply, smul_eq_mul]

lemma qrefl_qrefl (v : V) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hv : B v v = a + b) (z : V) :
    qrefl B v a (qrefl B v b z) = z := by
  rw [qrefl_apply, qrefl_apply, map_sub, map_smul, smul_eq_mul, hv, sub_sub, ← add_smul]
  have h : b⁻¹ * B v z + a⁻¹ * (B v z - b⁻¹ * B v z * (a + b)) = 0 := by
    field_simp
    ring
  rw [h, zero_smul, sub_zero]

lemma qrefl_isometry (hB : ∀ x y, star (B x y) = B y x) (v : V) (a : K) (ha : a ≠ 0)
    (hv : B v v = a + star a) (z w : V) :
    B (qrefl B v a z) (qrefl B v a w) = B z w := by
  have ha' : star a ≠ 0 := star_ne_zero.2 ha
  have key : ∀ p q r : K, p - a⁻¹ * q * r - (star a)⁻¹ * r * q +
      (star a)⁻¹ * r * (a⁻¹ * q) * (a + star a) = p := by
    intro p q r
    field_simp
    ring
  rw [qrefl_apply, qrefl_apply]
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    map_smul, starRingEnd_apply, RingHom.id_apply, star_mul', star_inv₀, hB, hv]
  linear_combination key (B z w) (B v w) (B z v)

def qreflEquiv (v : V) (a : K) (ha : a ≠ 0) (hv : B v v = a + star a) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (qrefl B v a) (qrefl B v (star a))
    (LinearMap.ext fun z => qrefl_qrefl B v a (star a) ha (by simpa using ha) hv z)
    (LinearMap.ext fun z => qrefl_qrefl B v (star a) a (by simpa using ha) ha
      (by rw [hv, add_comm]) z)

lemma oneVector_generic (hB : ∀ x y, star (B x y) = B y x) (x y : V) (hxy : B x x = B y y)
    (ha : B (x - y) x ≠ 0) :
    ∃ g : V ≃ₗ[K] V, (∀ z w, B (g z) (g w) = B z w) ∧ g x = y ∧
      ∀ z, B x z = 0 → B y z = 0 → g z = z := by
  have hv : B (x - y) (x - y) = B (x - y) x + star (B (x - y) x) := by
    rw [hB]
    simp only [map_sub, LinearMap.sub_apply]
    rw [← hxy]
    ring
  refine ⟨qreflEquiv B (x - y) (B (x - y) x) ha hv,
    fun z w => qrefl_isometry B hB (x - y) _ ha hv z w, ?_, fun z hz1 hz2 => ?_⟩
  · show qrefl B (x - y) (B (x - y) x) x = y
    rw [qrefl_apply, inv_mul_cancel₀ ha, one_smul, sub_sub_cancel]
  · show qrefl B (x - y) (B (x - y) x) z = z
    rw [qrefl_apply]
    simp only [map_sub, LinearMap.sub_apply, hz1, hz2, sub_zero, mul_zero, zero_smul]

end

theorem one_vector_holds : OneVector := by
  intro K V _ _ _ _ _ B hB x y hxy hx0
  by_cases ha : B (x - y) x ≠ 0
  · exact oneVector_generic B hB x y hxy ha
  · push_neg at ha
    have hyx : B y x = B x x := by
      have h : B (x - y) x = B x x - B y x := by simp only [map_sub, LinearMap.sub_apply]
      rw [h] at ha
      exact (sub_eq_zero.1 ha).symm
    have hxy' : B x x = B (-y) (-y) := by simp [hxy]
    have ha2 : B (x - -y) x ≠ 0 := by
      rw [sub_neg_eq_add, map_add (f := _), LinearMap.add_apply, hyx]
      intro h
      apply hx0
      have h2 : (2 : K) * B x x = 0 := by rw [two_mul]; exact h
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
    obtain ⟨g1, hg1, hg1x, hg1z⟩ := oneVector_generic B hB x (-y) hxy' ha2
    have hyy : B y y ≠ 0 := hxy ▸ hx0
    have ha0 : B y y / 2 ≠ 0 := div_ne_zero hyy two_ne_zero
    have hstar : star (B y y / 2) = B y y / 2 := by rw [star_div₀, hB, star_ofNat]
    have hv : B y y = B y y / 2 + star (B y y / 2) := by rw [hstar]; ring
    have h2 : (B y y / 2)⁻¹ * B y y = 2 := by field_simp
    refine ⟨g1.trans (qreflEquiv B y (B y y / 2) ha0 hv), fun z w => ?_, ?_, fun z hz1 hz2 => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      have hq : ∀ u, qreflEquiv B y (B y y / 2) ha0 hv u = qrefl B y (B y y / 2) u := fun _ => rfl
      rw [hq, hq, qrefl_isometry B hB y _ ha0 hv, hg1]
    · simp only [LinearEquiv.trans_apply, hg1x]
      show qrefl B y (B y y / 2) (-y) = y
      rw [qrefl_apply, map_neg, mul_neg, neg_smul, sub_neg_eq_add, h2, two_smul]
      abel
    · simp only [LinearEquiv.trans_apply]
      rw [hg1z z hz1 (by rw [map_neg, LinearMap.neg_apply, hz2, neg_zero])]
      show qrefl B y (B y y / 2) z = z
      rw [qrefl_apply, hz2, mul_zero, zero_smul, sub_zero]

end PI.Witt
end

