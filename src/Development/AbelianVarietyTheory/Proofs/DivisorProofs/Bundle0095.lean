module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefQuadraticAdjointPairBound
section
namespace GlobalTheory.PosFormAdjoint

theorem int_cauchy_schwarz {X : Type} [AddCommGroup X] (F : X →+ X →+ ℤ)
    (hsym : ∀ u v, F u v = F v u) (hpos : ∀ u, 0 ≤ F u u) (u v : X) :
    F u v ^ 2 ≤ F u u * F v v := by
  have key : ∀ a b : ℤ, 0 ≤ a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
    intro a b
    have h1 := hpos (a • u + b • v)
    have e : F (a • u + b • v) (a • u + b • v)
        = a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
      simp only [map_add (f := _), map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul]
      rw [hsym v u]
      ring
    rw [e] at h1
    exact h1
  rcases (hpos u).lt_or_eq with ht | ht
  · have h2 := key (-(F u v)) (F u u)
    have h3 : 0 ≤ F u u * (F u u * F v v - F u v ^ 2) := by nlinarith [h2]
    have h4 : 0 ≤ F u u * F v v - F u v ^ 2 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_neg_of_pos_of_neg ht hc]
    linarith
  · rw [← ht]
    simp only [zero_mul]
    by_contra hc
    push_neg at hc
    have hs : (1 : ℤ) ≤ F u v ^ 2 := hc
    have h2 := key (-(F v v + 1) * F u v) 1
    rw [← ht] at h2
    have hv := hpos v
    nlinarith [h2, hs, hv]

theorem seq_bound (a c : ℕ → ℤ) (n : ℕ) (hpos : ∀ k, 0 ≤ a k)
    (hlc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2))
    (hrec : a n + ∑ i ∈ Finset.range n, c i * a i = 0) :
    a 1 ≤ (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) * a 0 := by
  set S : ℤ := ∑ i ∈ Finset.range n, |c i| with hS
  have hcast : (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) = S + 1 := by
    push_cast
    simp [hS, Int.natCast_natAbs]
  rw [hcast]
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  by_contra H
  push_neg at H
  have ha0 : 0 < a 0 := by
    rcases (hpos 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hlc 0
      rw [← h] at h1 H
      simp at h1 H
      nlinarith [sq_nonneg (a 1)]
  have h01 : a 0 < a 1 := by nlinarith
  have hind : ∀ k, 0 < a k ∧ a 1 * a k ≤ a (k + 1) * a 0 := by
    intro k
    induction k with
    | zero => exact ⟨ha0, by simp [mul_comm]⟩
    | succ k ih =>
      obtain ⟨hk, hk'⟩ := ih
      have hk1 : 0 < a (k + 1) := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos (by linarith : (0:ℤ) < a 1) hk]
      refine ⟨hk1, ?_⟩
      have h2 := hlc k
      have h3 : a k * (a 1 * a (k + 1)) ≤ a k * (a (k + 2) * a 0) := by
        nlinarith [mul_le_mul_of_nonneg_left hk' hk1.le]
      exact le_of_mul_le_mul_left h3 hk
  have hmono : ∀ k, a k ≤ a (k + 1) := by
    intro k
    obtain ⟨hk, hk'⟩ := hind k
    have : a 0 * a k ≤ a 0 * a (k + 1) := by nlinarith [mul_le_mul_of_nonneg_right h01.le hk.le]
    exact le_of_mul_le_mul_left this ha0
  have hmono' : Monotone a := monotone_nat_of_le_succ hmono
  rcases n with _ | m
  · simp at hrec
    linarith
  · rw [Finset.sum_range_succ] at hrec
    obtain ⟨hm, hm'⟩ := hind m
    have hle : -(∑ i ∈ Finset.range (m + 1), c i * a i) ≤ S * a m := by
      rw [hS, Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h1 : -(c i * a i) ≤ |c i| * a i := by
        have := neg_abs_le (c i)
        nlinarith [hpos i]
      have h2 : |c i| * a i ≤ |c i| * a m :=
        mul_le_mul_of_nonneg_left (hmono' hi') (abs_nonneg _)
      linarith
    have hrec' : a (m + 1) = -(∑ i ∈ Finset.range (m + 1), c i * a i) := by
      rw [Finset.sum_range_succ]; linarith
    have h5 : (S + 1) * a 0 * a m < a 1 * a m := by nlinarith
    have h6 : (S + 1) * a m * a 0 < a (m + 1) * a 0 := by nlinarith
    have h7 : (S + 1) * a m < a (m + 1) := lt_of_mul_lt_mul_right h6 ha0.le
    nlinarith

end GlobalTheory.PosFormAdjoint

namespace GlobalTheory.PosFormAdjoint

theorem pos_form_adjoint_bound : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y := by
  intro X _ _ _ h h'
  let T : Module.End ℤ X := h'.toIntLinearMap * h.toIntLinearMap
  have hT : ∀ u, T u = h' (h u) := fun u => rfl
  let p := T.charpoly
  refine ⟨(∑ i ∈ Finset.range p.natDegree, (-(p.coeff i)).natAbs) + 1, ?_⟩
  intro q hq hq0 hqneg hcube hadj y
  let B : X →+ X →+ ℤ := AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun v => q (u + v) - q u - q v)
      (fun a b => by
        have := hcube u a b
        rw [← add_assoc]
        linarith))
    (fun a b => by
      ext v
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      have := hcube a b v
      linarith)
  have hB : ∀ u v, B u v = q (u + v) - q u - q v := fun u v => rfl
  have Bsym : ∀ u v, B u v = B v u := by
    intro u v; rw [hB, hB, add_comm]; ring
  have Bdiag : ∀ u, B u u = 2 * q u := by
    intro u
    have := hcube u u (-u)
    simp only [add_neg_cancel_right, add_neg_cancel, hq0, hqneg] at this
    rw [hB]; linarith
  have Badj : ∀ u v, B (h u) v = B u (h' v) := by
    intro u v; rw [hB, hB]; have := hadj u v; linarith
  have BT : ∀ u v, B (T u) v = B u (T v) := by
    intro u v
    rw [hT, hT, Bsym, ← Badj, Bsym, Badj]
  have BTpow : ∀ k u v, B ((T ^ k) u) v = B u ((T ^ k) v) := by
    intro k
    induction k with
    | zero => intro u v; rfl
    | succ k ih =>
      intro u v
      rw [pow_succ', Module.End.mul_apply, BT, ih]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ, ← pow_succ']
  let G : X →+ X →+ ℤ := B.comp (T : X →+ X)
  have hG : ∀ u v, G u v = B (T u) v := fun u v => rfl
  have Gsym : ∀ u v, G u v = G v u := by
    intro u v; rw [hG, hG, BT, Bsym]
  have Gdiag : ∀ u, G u u = 2 * q (h u) := by
    intro u; rw [hG, hT, Bsym, ← Badj, Bdiag]
  have Bpos : ∀ u, 0 ≤ B u u := fun u => by rw [Bdiag]; linarith [hq u]
  have Gpos : ∀ u, 0 ≤ G u u := fun u => by rw [Gdiag]; linarith [hq (h u)]
  let a : ℕ → ℤ := fun k => B ((T ^ k) y) y
  have aB : ∀ i j, a (i + j) = B ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    show B ((T ^ (i + j)) y) y = _
    rw [pow_add, Module.End.mul_apply, BTpow]
    exact Bsym _ _
  have aG : ∀ i j, a (i + j + 1) = G ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    rw [hG, ← Module.End.mul_apply, ← pow_succ', add_right_comm, aB]
  have apos : ∀ k, 0 ≤ a k := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [two_mul, aB]; exact Bpos _
    · rw [two_mul, aG]; exact Gpos _
  have alc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2) := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have e1 : a (2 * m + 1) = B ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      have e2 : a (2 * m + 2) = B ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      rw [e1, e2, two_mul, aB]
      exact int_cauchy_schwarz B Bsym Bpos _ _
    · have e1 : a (2 * m + 1 + 1) = G ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      have e2 : a (2 * m + 1 + 2) = G ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      rw [e1, e2, two_mul, aG]
      exact int_cauchy_schwarz G Gsym Gpos _ _
  have hmonic : p.Monic := LinearMap.charpoly_monic T
  have hrec : a p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * a i = 0 := by
    have hCH : (Polynomial.aeval T p) y = 0 := by
      rw [LinearMap.aeval_self_charpoly]; rfl
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul] at hCH
    have h2 := congrArg (fun x => B x y) hCH
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add (f := _),
      map_sum, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply,
      AddMonoidHom.smul_apply, smul_eq_mul, map_zero, AddMonoidHom.zero_apply] at h2
    rw [add_comm]; exact h2
  have hb := seq_bound a (fun i => p.coeff i) p.natDegree apos alc hrec
  have a0 : a 0 = 2 * q y := by show B ((T ^ 0) y) y = _; rw [pow_zero]; exact Bdiag y
  have a1 : a 1 = 2 * q (h y) := by
    have := aG 0 0
    simp only [zero_add, pow_zero] at this
    rw [this]; exact Gdiag y
  rw [a0, a1] at hb
  have habs : ∀ i, (-(p.coeff i)).natAbs = (p.coeff i).natAbs := fun i => Int.natAbs_neg _
  simp only [habs]
  linarith

end GlobalTheory.PosFormAdjoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.ConvSeries

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def wt (b c : ℝ) (h : E → ℂ) (a : E) : ℂ :=
  Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖a‖ ^ 2 : ℝ) : ℂ))

def innerC (a : E) : E →L[ℝ] ℂ := Complex.ofRealCLM ∘L innerSL ℝ a

def powForm (k : ℕ) (a : E) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ).compContinuousLinearMap fun _ => innerC a

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def coef (b c : ℝ) (h : E → ℂ) (k : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
  ∫ a, wt b c h a • powForm k a

def term (b c : ℝ) (h : E → ℂ) (k : ℕ) (y : E) : ℂ :=
  Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * (((2 * c) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
    coef b c h k (fun _ => y)

end GlobalTheory.ConvSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMapsTorsionIntoSmulTop
section
namespace GlobalTheory


open Submodule in
theorem pow_maps_torsion_into_smul_top (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type)
    [AddCommGroup M] [Module R M] (I J : Ideal R) (f : M →ₗ[R] M) (m : ℕ) :
    I.IsMaximal → J ≠ ⊥ → (∀ x, (f ^ m) x ∈ I • (⊤ : Submodule R M)) →
      ∃ j : ℕ, ∀ y : M, (∀ a ∈ I, a • y ∈ J • (⊤ : Submodule R M)) →
        (f ^ j) y ∈ J • (⊤ : Submodule R M) := by
  intro hI hJ hf
  obtain ⟨Q, hIQ, hJQ⟩ := Ideal.eq_prime_pow_mul_coprime hJ I
  set k := Multiset.count I (UniqueFactorizationMonoid.normalizedFactors J)

  have hstab : ∀ (n : ℕ) (z : M), z ∈ J • (⊤ : Submodule R M) → (f ^ n) z ∈ J • (⊤ : Submodule R M) := by
    intro n z hz
    have : (J • (⊤ : Submodule R M)).map (f ^ n) ≤ J • (⊤ : Submodule R M) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨z, hz, rfl⟩

  have hmap : (⊤ : Submodule R M).map (f ^ m) ≤ I • (⊤ : Submodule R M) := by
    rintro _ ⟨x, -, rfl⟩
    exact hf x
  have hpow : ∀ (i : ℕ) (x : M), (f ^ (m * i)) x ∈ I ^ i • (⊤ : Submodule R M) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      have h1 : (f ^ (m * (i + 1))) x = (f ^ m) ((f ^ (m * i)) x) := by
        rw [Nat.mul_succ, add_comm, pow_add, Module.End.mul_apply]
      rw [h1]
      have h2 : (I ^ i • (⊤ : Submodule R M)).map (f ^ m) ≤ I ^ (i + 1) • (⊤ : Submodule R M) := by
        rw [Submodule.map_smul'', pow_succ, Submodule.mul_smul]
        exact Submodule.smul_mono le_rfl hmap
      exact h2 ⟨_, ih x, rfl⟩
  refine ⟨m * k, fun y hy => ?_⟩
  set Z := (f ^ (m * k)) y with hZ
  have hZk : Z ∈ I ^ k • (⊤ : Submodule R M) := hpow k y
  have hIZ : ∀ a ∈ I, a • Z ∈ J • (⊤ : Submodule R M) := by
    intro a ha
    rw [hZ, ← LinearMap.map_smul]
    exact hstab _ _ (hy a ha)
  have hJle : J ≤ Q := by rw [hJQ]; exact Ideal.mul_le_inf.trans inf_le_right
  have hZQ : Z ∈ Q • (⊤ : Submodule R M) := by
    have h1 : (1 : R) ∈ I ⊔ Q := by rw [hIQ]; trivial
    obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.1 h1
    have : Z = t • Z + s • Z := by rw [← add_smul, hts, one_smul]
    rw [this]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem_smul hs trivial)
    exact Submodule.smul_mono_left hJle (hIZ t ht)
  have hkQ : I ^ k ⊔ Q = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at hIQ ⊢
    exact hIQ.pow_left
  have h1 : (1 : R) ∈ I ^ k ⊔ Q := by rw [hkQ]; trivial
  obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.1 h1
  have : Z = t • Z + s • Z := by rw [← add_smul, hts, one_smul]
  rw [this]
  refine Submodule.add_mem _ ?_ ?_
  · have : t • Z ∈ I ^ k • Q • (⊤ : Submodule R M) := Submodule.smul_mem_smul ht hZQ
    rwa [← Submodule.mul_smul, ← hJQ] at this
  · have : s • Z ∈ Q • I ^ k • (⊤ : Submodule R M) := Submodule.smul_mem_smul hs hZk
    rwa [← Submodule.mul_smul, mul_comm, ← hJQ] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfFiniteAppLE
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem preimage_eq_of_finite_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π] {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → IsAffineOpen V → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (π.appLE U V h).hom.Finite → π ⁻¹ᵁ U = V := by
  intro X Y _ π _ U V hU hV hne h hfin
  have : IsAffine U := hU
  have : IsAffine V := hV
  have hf : IsFinite (π.resLE U V h) := by
    have hS : IsFinite (Spec.map (π.resLE U V h).appTop) := (IsFinite.SpecMap_iff _).mpr
      ((RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso π U V h)).mpr hfin)
    rw [Arrow.iso_w' (arrowIsoSpecΓOfIsAffine (π.resLE U V h)).symm]
    infer_instance
  have : UniversallyClosed (Y.homOfLE h ≫ π ∣_ U) := by
    change UniversallyClosed (π.resLE U V h)
    infer_instance
  have : UniversallyClosed (Y.homOfLE h) := .of_comp_of_isSeparated _ (π ∣_ U)
  obtain ⟨y, hy⟩ := hne
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨y, h hy⟩⟩
  have hcl : IsClopen (Set.range (Y.homOfLE h).base) :=
    ⟨(Y.homOfLE h).isClosedMap.isClosed_range,
      (Y.homOfLE h).isOpenEmbedding.isOpenMap.isOpen_range⟩
  have huniv : Set.range (Y.homOfLE h).base = Set.univ :=
    (isClopen_iff.mp hcl).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨_, ⟨⟨y, hy⟩, rfl⟩⟩)
  refine le_antisymm (fun x hx => ?_) h
  obtain ⟨⟨w, hw⟩, hz⟩ : (⟨x, hx⟩ : π ⁻¹ᵁ U) ∈ Set.range (Y.homOfLE h).base := by
    rw [huniv]; trivial
  have hz' : ((Y.homOfLE h) ⟨w, hw⟩).1 = x := congrArg Subtype.val hz
  have hzx : w = x := (Scheme.homOfLE_apply h ⟨w, hw⟩).symm.trans hz'
  exact hzx ▸ hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceTensorOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isPullback_comp_mono_right_of_isPullback {𝒞 : Type*} [Category 𝒞] {P X Y Z Z' : 𝒞} {fst : P ⟶ X} {snd : P ⟶ Y}
    {a : X ⟶ Z} {b : Y ⟶ Z} (m : Z ⟶ Z') [Mono m] (h : IsPullback fst snd a b) :
    IsPullback fst snd (a ≫ m) (b ≫ m) :=
  ⟨⟨by rw [← Category.assoc, h.w, Category.assoc]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ h.lift c.fst c.snd (by rw [← cancel_mono m]; simpa using c.condition))
    (fun c ↦ h.lift_fst _ _ _) (fun c ↦ h.lift_snd _ _ _)
    (fun c n h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, h₁]) (by rw [h.lift_snd, h₂]))⟩⟩

theorem preirreducibleSpace_tensor_of_pullback :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V)
      (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k]
      [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom →
      PreirreducibleSpace ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  intro X S f V W h hV hW k _ _ _ hA hP
  have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, V) k Γ(X, W))).flip
  have sq2 := sq.of_iso (fst' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
      hW.isoSpec.inv) (snd' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (f' := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))))
    (g' := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)))
    (Iso.refl _) hW.isoSpec.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)
  have sq3 := isPullback_comp_mono_right_of_isPullback hV.fromSpec sq2
  have e : (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W)))) ≫
      hV.fromSpec = W.ι ≫ f := by
    rw [hA, CommRingCat.ofHom_hom, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hV hW h,
      ← hW.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]
  rw [e] at sq3
  let φ := sq3.isoPullback
  have hsurj : Function.Surjective (Scheme.homeoOfIso φ.symm) := (Scheme.homeoOfIso φ.symm).surjective
  refine ⟨?_⟩
  have := (PreirreducibleSpace.isPreirreducible_univ (X := ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)))).image
    (Scheme.homeoOfIso φ.symm) (Scheme.homeoOfIso φ.symm).continuous.continuousOn
  rw [Set.image_univ_of_surjective hsurj] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleTensorLocalizationAway
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preirreducibleSpace_primeSpectrum_tensor_localizationAway
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k]
    [Algebra A k] :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by
  intro hX
  letI : Algebra (k ⊗[A] B) (k ⊗[A] Localization.Away b) :=
    (Algebra.TensorProduct.map (AlgHom.id A k)
      (IsScalarTower.toAlgHom A B (Localization.Away b))).toAlgebra
  haveI : IsScalarTower k (k ⊗[A] B) (k ⊗[A] Localization.Away b) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right A k (Submonoid.powers b)
    (Localization.Away b) (by ext; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at hl
  haveI : IsLocalization.Away
      (Algebra.TensorProduct.includeRight (R := A) (A := k) b) (k ⊗[A] Localization.Away b) := hl
  exact (PrimeSpectrum.localization_away_isOpenEmbedding (k ⊗[A] Localization.Away b)
    (Algebra.TensorProduct.includeRight (R := A) (A := k) b)).preirreducibleSpace

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveVectorQuadraticLevelMeasure
section
namespace GlobalTheory

theorem residue_surj_localizationAway : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal D) (g : D), g ∉ Q → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Q.map (algebraMap D (Localization.Away g)) := by
  intro B D _ _ _ P hP Q g hg hQP hsurj a
  obtain ⟨⟨d, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) a
  obtain ⟨n, hn⟩ := s.2
  obtain ⟨bd, hbd⟩ := hsurj d
  obtain ⟨bg, hbg⟩ := hsurj g
  have hbgP : bg ∉ P := by
    intro h
    rw [← hQP, Ideal.mem_comap] at h
    exact hg (by simpa using Q.add_mem hbg h)
  obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbgP
  have hcg : algebraMap B D c * g - 1 ∈ Q := by
    have hiQ : algebraMap B D i ∈ Q := by rw [← hQP] at hi; exact hi
    have e : algebraMap B D c * g - 1 = algebraMap B D c * (g - algebraMap B D bg) - algebraMap B D i := by
      have := congrArg (algebraMap B D) hci
      simp only [map_add (f := _), map_mul, map_one] at this
      linear_combination this
    rw [e]
    exact Q.sub_mem (Q.mul_mem_left _ hbg) hiQ
  refine ⟨bd * c ^ n, ?_⟩
  have key : d - algebraMap B D (bd * c ^ n) * (s : D) ∈ Q := by
    rw [← hn]
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hcg hbd ⊢
    simp only [map_sub, map_mul, map_pow, map_one, sub_eq_zero] at hcg hbd ⊢
    rw [hbd, mul_assoc, ← mul_pow, hcg, one_pow, mul_one]
  set L := Localization.Away g
  have hspec : algebraMap D L (s : D) * IsLocalization.mk' L (1 : D) s = 1 := by
    rw [IsLocalization.mk'_spec', map_one]
  have e : IsLocalization.mk' L d s - algebraMap B L (bd * c ^ n)
      = algebraMap D L (d - algebraMap B D (bd * c ^ n) * (s : D)) * IsLocalization.mk' L (1 : D) s := by
    rw [IsScalarTower.algebraMap_apply B D L, IsLocalization.mk'_eq_mul_mk'_one, map_sub, map_mul (algebraMap D L)]
    linear_combination (algebraMap D L (algebraMap B D (bd * c ^ n))) * hspec
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ key)

end GlobalTheory
end

