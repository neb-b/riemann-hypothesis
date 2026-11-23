module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicHermitianFormGaloisMemOfMemCompletion
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

theorem hermA_tmul_right (z : Fin n → RA F E) (t : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    hermA c G z (fun i => t ⊗ₜ[F] x i) = (t ⊗ₜ[F] (1 : E)) * hermA c G z (fv F x) := by
  simp only [hermA, fv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : sg (FiniteAdeleRing (𝓞 F) F) c (t ⊗ₜ[F] x b) = (t ⊗ₜ[F] (1 : E)) *
      sg (FiniteAdeleRing (𝓞 F) F) c ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x b) := by
    simp [sg, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h]; ring

theorem hermA_fv_fv (x y : Fin n → E) :
    hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) := by
  simp [hermA, fv, sg, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sum]

theorem adelicHermitianFormGalois_mem_of_mem_completion {S : Set (Fin n → E)} {J : Set E} {z : Fin n → RA F E}
    (hz : ∀ y ∈ S, hermA c G z (fv F y) ∈ hat1 F J) {w : Fin n → RA F E} (hw : w ∈ hat F S) :
    hermA c G z w ∈ hat1 F J := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨t, ht, x, hx, rfl⟩ := hw
    rw [hermA_tmul_right]
    exact mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := {1}) (fun a ha b hb => by
      rw [Set.mem_singleton_iff.1 ha, one_mul]; exact hb) (tmul_mem_adelicCompletion_of_integral F ht rfl) (hz x hx)
  | zero =>
    have : hermA c G z 0 = 0 := by simp [hermA]
    rw [this]; exact zero_mem _
  | add w w' _ _ h h' =>
    have : hermA c G z (w + w') = hermA c G z w + hermA c G z w' := by
      simp only [hermA, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
    rw [this]; exact add_mem h h'
  | neg w _ h =>
    have : hermA c G z (-w) = - hermA c G z w := by
      simp only [hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
    rw [this]; exact neg_mem h

end

theorem latOf_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) → G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) → (∀ x y, hermA c G ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ x) ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ y) = hermA c G x y) → ∀ v : Fin n → E, (∀ y ∈ latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L := by
  intro F E _ _ _ _ _ n L c G J g hfg hspan hc hG hdet hJ hL hg v
  have hd := _root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hfg hspan hc hG hdet hJ hL
  obtain ⟨Λ, hΛ, -, -, hhat⟩ := _root_.GlobalTheory.AdLat.exists_lattice_latOf F E n L g hfg hspan
  constructor
  · intro hv
    have hz : (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ
        (((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F v) = fv F v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨_, (hd _).1 fun y hy => ?_, hz⟩
    rw [← hg, hz]
    refine adelicHermitianFormGalois_mem_of_mem_completion c G (S := (Λ : Set (Fin n → E))) (fun y' hy' => ?_) ?_
    · rw [hermA_fv_fv]
      exact one_tmul_mem_adelicCompletionOfElementSet F (hv y' (hΛ ▸ hy'))
    · have : (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F y ∈
          (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) := by
        rw [hhat]
        exact ⟨fv F y, AddSubgroup.subset_closure ⟨1, adele_one_integral F, y, hy, rfl⟩, rfl⟩
      exact this
  · rintro ⟨z, hz, hzv⟩ y ⟨w, hw, hwy⟩
    rw [← one_tmul_mem_adelicCompletion_fractionalIdeal_iff F, ← hermA_fv_fv, ← hzv, ← hwy, hg]
    exact adelicHermitianFormGalois_mem_of_mem_completion c G ((hd z).2 hz) hw

end GlobalTheory.AdLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLinearApproxTower
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Tower

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i; simp [fv, TensorProduct.tmul_add]

omit [NumberField E] in
lemma fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  funext i; simp [fv, TensorProduct.tmul_sub]

omit [NumberField E] in
lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i; simp [fv]

omit [NumberField E] in
lemma fv_nsmul (N : ℕ) (x : Fin n → E) : fv F (N • x) = N • fv F x := by
  induction N with
  | zero => simp [fv_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]

omit [NumberField E] in
lemma fv_smul (c : 𝓞 E) (x : Fin n → E) :
    fv F (c • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • fv F x := by
  funext i
  simp only [fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

omit [NumberField E] in
lemma nsmul_cancel {N : ℕ} (hN : 0 < N) {z u : Fin n → RA F E} (h : N • z = N • u) : z = u := by
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have := congrArg (fun t => (N : F)⁻¹ • t) h
  simpa [smul_smul, inv_mul_cancel₀ hN'] using this

omit [NumberField E] in
lemma smul_mem_hat (L : Submodule (𝓞 E) (Fin n → E)) (c : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma exists_div {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : ∀ v, fv F v ∈ hat F (M : Set (Fin n → E)) ↔ v ∈ M) {N : ℕ} (hN : 0 < N)
    (x : M) {u : Fin n → RA F E} (hu : u ∈ hat F (M : Set (Fin n → E)))
    (h : fv F (x : Fin n → E) = N • u) : ∃ v : M, x = N • v := by
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : N • ((N : E)⁻¹ • (x : Fin n → E)) = x := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hN', one_smul]
  have h2 : fv F ((N : E)⁻¹ • (x : Fin n → E)) = u := by
    apply nsmul_cancel hN
    rw [← fv_nsmul, h1, h]
  refine ⟨⟨_, (hM _).1 (h2 ▸ hu)⟩, Subtype.ext ?_⟩
  exact h1.symm

lemma projective_of_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Module.Projective (𝓞 E) L := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 E) L := inferInstance
  exact Module.Flat.projective_of_finitePresentation

omit [NumberField E] in
lemma mulVec_nsmul (g : Matrix (Fin n) (Fin n) (RA F E)) (N : ℕ) (z : Fin n → RA F E) :
    g *ᵥ (N • z) = N • (g *ᵥ z) := map_nsmul g.mulVecLin N z

def rel (L Λ : Submodule (𝓞 E) (Fin n → E)) (g : Matrix (Fin n) (Fin n) (RA F E)) (N : ℕ) :
    Submodule (𝓞 E) (L × Λ) where
  carrier := {p | ∃ w ∈ hat F (L : Set (Fin n → E)),
    fv F (p.2 : Fin n → E) = g *ᵥ (fv F (p.1 : Fin n → E) + N • w)}
  zero_mem' := ⟨0, zero_mem _, by simp [fv_zero]⟩
  add_mem' := by
    rintro p q ⟨w, hw, hp⟩ ⟨w', hw', hq⟩
    refine ⟨w + w', add_mem hw hw', ?_⟩
    simp only [Prod.snd_add, Prod.fst_add, Submodule.coe_add, fv_add, hp, hq]
    rw [← Matrix.mulVec_add, smul_add]
    congr 1
    abel
  smul_mem' := by
    rintro c p ⟨w, hw, hp⟩
    refine ⟨_, smul_mem_hat L c hw, ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul, fv_smul, hp]
    rw [← Matrix.mulVec_smul, smul_add, smul_comm]

end GlobalTheory.AdLat.Tower

open GlobalTheory.AdLat.Tower in
theorem GlobalTheory.AdLat.exists_linear_approx_tower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (Λ : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L → ∃ f : ℕ → (L →ₗ[𝓞 E] Λ), (∀ N : ℕ, 0 < N → ∀ a : L, ∃ w ∈ (hat F (L : Set (Fin n → E))), fv F (f N a : Fin n → E) = (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ (fv F (a : Fin n → E) + N • w)) ∧ (∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ v, f (N * m) a = f N a + N • v) ∧ ∀ N : ℕ, 0 < N → (∀ a, (∃ v, f N a = N • v) ↔ ∃ v, a = N • v) ∧ ∀ a', ∃ a v, a' = f N a + N • v := by
  intro F E _ _ _ _ _ n L g Λ hL hsp hΛ
  obtain ⟨Λ', h1, hΛfg, hΛsp, hhat⟩ := _root_.GlobalTheory.AdLat.exists_lattice_latOf F E n L g hL hsp
  obtain rfl : Λ = Λ' := SetLike.coe_injective (hΛ.trans h1.symm)
  obtain ⟨hLc, hLa, -, -⟩ := _root_.GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hsp
  obtain ⟨hΛc, hΛa, -, -⟩ := _root_.GlobalTheory.AdLat.hat_rational_points_and_approx F E n Λ hΛfg hΛsp
  set G : Matrix (Fin n) (Fin n) (RA F E) := g.val with hG
  have hto : ∀ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u ∈ hat F (Λ : Set (Fin n → E)) := by
    intro u hu
    rw [← SetLike.mem_coe, hhat]
    exact ⟨u, hu, rfl⟩
  have hfrom : ∀ z ∈ hat F (Λ : Set (Fin n → E)), ∃ u ∈ hat F (L : Set (Fin n → E)), G *ᵥ u = z := by
    intro z hz
    rw [← SetLike.mem_coe, hhat] at hz
    exact hz
  have hinj : ∀ u u' : Fin n → RA F E, G *ᵥ u = G *ᵥ u' → u = u' := by
    intro u u' h
    have := congrArg (fun t => ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ t) h
    simp only [hG, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
    exact this
  haveI := projective_of_fg L hL
  have key : ∀ N : ℕ, ∃ f : L →ₗ[𝓞 E] Λ, 0 < N → ∀ a : L, ∃ w ∈ hat F (L : Set (Fin n → E)),
      fv F (f a : Fin n → E) = G *ᵥ (fv F (a : Fin n → E) + N • w) := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · exact ⟨0, fun h => absurd h (by omega)⟩
    have hsurj : Function.Surjective
        ((LinearMap.fst (𝓞 E) L Λ).comp (rel L Λ G N).subtype) := by
      intro a
      obtain ⟨x, hx, w, hw, e⟩ := hΛa N hN _ (hto _ ((hLc a).2 a.2))
      obtain ⟨u, hu, rfl⟩ := hfrom w hw
      refine ⟨⟨(a, ⟨x, hx⟩), -u, neg_mem hu, ?_⟩, rfl⟩
      rw [Matrix.mulVec_add, mulVec_nsmul, Matrix.mulVec_neg, e]
      simp
    obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
    refine ⟨(LinearMap.snd (𝓞 E) L Λ).comp ((rel L Λ G N).subtype.comp s), fun _ a => ?_⟩
    obtain ⟨w, hw, e⟩ := (s a).2
    have ha : (s a).1.1 = a := LinearMap.congr_fun hs a
    rw [ha] at e
    exact ⟨w, hw, e⟩
  choose f hf using key
  refine ⟨f, hf, ?_, ?_⟩
  · intro N m hN hm a
    obtain ⟨w, hw, e⟩ := hf N hN a
    obtain ⟨w', hw', e'⟩ := hf (N * m) (Nat.mul_pos hN hm) a
    obtain ⟨v, hv⟩ := exists_div hΛc hN (f (N * m) a - f N a)
      (hto _ (sub_mem (nsmul_mem hw' m) hw)) (by
        rw [Submodule.coe_sub, fv_sub, e, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub,
          mul_smul]
        congr 1
        abel)
    exact ⟨v, by rw [← hv]; abel⟩
  · intro N hN
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw, e⟩ := hf N hN a
      obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc v).2 v.2)
      have e2 : fv F (f N a : Fin n → E) = G *ᵥ (N • u) := by
        rw [mulVec_nsmul, eu, ← fv_nsmul, hv]; rfl
      have e3 := hinj _ _ (e.symm.trans e2)
      exact exists_div hLc hN a (sub_mem hu hw) (by rw [smul_sub, ← e3]; abel)
    · rintro ⟨v, rfl⟩
      exact ⟨f N v, map_nsmul _ _ _⟩
    · obtain ⟨u, hu, eu⟩ := hfrom _ ((hΛc a').2 a'.2)
      obtain ⟨x, hx, w, hw, rfl⟩ := hLa N hN u hu
      obtain ⟨w', hw', e'⟩ := hf N hN ⟨x, hx⟩
      obtain ⟨v, hv⟩ := exists_div hΛc hN (a' - f N ⟨x, hx⟩) (hto _ (sub_mem hw hw')) (by
        rw [Submodule.coe_sub, fv_sub, ← eu, e', ← mulVec_nsmul, ← Matrix.mulVec_sub, smul_sub]
        congr 1
        abel)
      exact ⟨⟨x, hx⟩, v, by rw [← hv]; abel⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Half

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_add_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (x + x') y =
      _root_.GlobalTheory.AdLat.hermA c G x y + _root_.GlobalTheory.AdLat.hermA c G x' y :=
  _root_.GlobalTheory.AdLat.hermA_add_left c G x x' y

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_add_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x y y' : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (y + y') =
      _root_.GlobalTheory.AdLat.hermA c G x y + _root_.GlobalTheory.AdLat.hermA c G x y' := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
lemma _root_.GlobalTheory.AdLat.Half.herm_sub_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (x - x') y =
      _root_.GlobalTheory.AdLat.hermA c G x y - _root_.GlobalTheory.AdLat.hermA c G x' y := by
  rw [sub_eq_add_neg, _root_.GlobalTheory.AdLat.hermA_add_left, _root_.GlobalTheory.AdLat.hermA_neg_left,
    ← sub_eq_add_neg]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
lemma _root_.GlobalTheory.AdLat.Half.herm_neg_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (-y) = -_root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
lemma _root_.GlobalTheory.AdLat.Half.herm_sub_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x y y' : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (y - y') =
      _root_.GlobalTheory.AdLat.hermA c G x y - _root_.GlobalTheory.AdLat.hermA c G x y' := by
  rw [sub_eq_add_neg, _root_.GlobalTheory.AdLat.Half.herm_add_right, _root_.GlobalTheory.AdLat.Half.herm_neg_right,
    ← sub_eq_add_neg]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_smul_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (r : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (r • x) y = r * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_smul_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (r : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (r • y) =
      _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c r * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_mem_of_fv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : Set E) (L : Set (Fin n → E)) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E)
    (hz : ∀ y ∈ L, _root_.GlobalTheory.AdLat.hermA c G z (_root_.GlobalTheory.AdLat.fv F y) ∈
      _root_.GlobalTheory.AdLat.hat1 F J)
    (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) (hw : w ∈ _root_.GlobalTheory.AdLat.hat F L) :
    _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F J := by
  unfold _root_.GlobalTheory.AdLat.hat at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hw
    have hw' : (fun i => a ⊗ₜ[F] y i) =
        (a ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • _root_.GlobalTheory.AdLat.fv F y := by
      funext i
      simp [_root_.GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hw', _root_.GlobalTheory.AdLat.Half.herm_smul_right]
    have hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] (1 : E)) =
        a ⊗ₜ[F] (1 : E) := by
      simp [_root_.GlobalTheory.AdLat.sg]
    rw [hsg]
    refine _root_.GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := {1}) (fun x hx y hy => ?_)
      (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F ha rfl) (hz y hy)
    rw [Set.mem_singleton_iff.1 hx, one_mul]
    exact hy
  | zero =>
    have h0 : _root_.GlobalTheory.AdLat.hermA c G z 0 = 0 := by
      simp [_root_.GlobalTheory.AdLat.hermA]
    rw [h0]
    exact zero_mem _
  | add w w' _ _ hw hw' =>
    rw [_root_.GlobalTheory.AdLat.Half.herm_add_right]
    exact add_mem hw hw'
  | neg w _ hw =>
    rw [_root_.GlobalTheory.AdLat.Half.herm_neg_right]
    exact neg_mem hw

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.fv_mem_hat' (L : Set (Fin n → E)) (y : Fin n → E)
    (hy : y ∈ L) : _root_.GlobalTheory.AdLat.fv F y ∈ _root_.GlobalTheory.AdLat.hat F L :=
  AddSubgroup.subset_closure ⟨1, _root_.GlobalTheory.AdLat.adele_one_integral F, y, hy, rfl⟩

end GlobalTheory.AdLat.Half

namespace GlobalTheory.AdLat

open Half

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
theorem _root_.GlobalTheory.AdLat.trivial_level_of_half : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E)
    (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E)
    (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (M : ℕ) (I I' : Ideal (𝓞 E)), L.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) →
    G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) →
    (∀ x y, _root_.GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ y) = _root_.GlobalTheory.AdLat.hermA c G x y) →
    0 < M → I ⊔ I' = ⊤ → I * I' = Ideal.span {(M : 𝓞 E)} →
    (∀ b ∈ I', ∃ b' ∈ I, ((b' : 𝓞 E) : E) = c (b : E)) →
    (∀ b ∈ I, ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) -
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) = M • y) →
    ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ z - z = M • y := by
  intro F E _ _ _ _ _ n L c G J g M I I' hFG hspan hc hG hdet hJ hdual hg hM hsup hprod hcI hhalf
  set Lh := _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) with hLh
  generalize (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) = gm at hg hhalf ⊢
  let e : 𝓞 E → _root_.GlobalTheory.AdLat.RA F E :=
    fun b => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)
  have hh : ∀ b ∈ I, ∀ z ∈ Lh, ∃ y ∈ Lh, gm *ᵥ (e b • z) - e b • z = M • y := hhalf
  have hu : ∀ (r : _root_.GlobalTheory.AdLat.RA F E) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E),
      gm *ᵥ (r • z) - r • z = r • (gm *ᵥ z - z) := fun r z => by
    rw [Matrix.mulVec_smul, smul_sub]
  have hM0 : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hnat : ∀ (m : ℕ) (v : Fin n → _root_.GlobalTheory.AdLat.RA F E),
      m • v = (algebraMap F (_root_.GlobalTheory.AdLat.RA F E) m) • v := fun m v => by
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hMcancel : ∀ x y : Fin n → _root_.GlobalTheory.AdLat.RA F E, M • x = M • y → x = y := by
    intro x y hxy
    rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at hxy
    exact smul_right_injective _ hM0 hxy
  have heM : e (M : 𝓞 E) = algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M := by
    simp only [e, map_natCast]
    push_cast
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  have hMI : (M : 𝓞 E) ∈ I := by
    have h1 : (M : 𝓞 E) ∈ Ideal.span {(M : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← hprod] at h1
    have h2 : I * I' ≤ I := Ideal.mul_le_left
    exact h2 h1

  have hstab : ∀ z ∈ Lh, gm *ᵥ z - z ∈ Lh := fun z hz => by
    obtain ⟨y, hy, hyz⟩ := hh _ hMI z hz
    rw [hu, heM, ← hnat] at hyz
    rw [hMcancel _ _ hyz]
    exact hy
  have hgL : ∀ z ∈ Lh, gm *ᵥ z ∈ Lh := fun z hz => by
    rw [← sub_add_cancel (gm *ᵥ z) z]
    exact add_mem (hstab z hz) hz
  have hpair : ∀ z ∈ Lh, ∀ w ∈ Lh,
      _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F (J : Set E) :=
    fun z hz w hw => _root_.GlobalTheory.AdLat.Half.herm_mem_of_fv c G J L z
      ((_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual z).2
        hz) w hw
  intro z hz
  obtain ⟨i, hi, i', hi', hii'⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ I')
  obtain ⟨b, hb, hbc⟩ := hcI i' hi'
  have he1 : e i + e i' = 1 := by
    have h1 : (i : E) + (i' : E) = 1 := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hii'
    simp only [e, ← TensorProduct.tmul_add]
    rw [h1]
    rfl
  set w := gm *ᵥ z - z with hw
  obtain ⟨y₁, hy₁, hwy₁⟩ := hh i hi z hz
  rw [hu] at hwy₁
  set v : Fin n → _root_.GlobalTheory.AdLat.RA F E := ((M : F)⁻¹) • (e i' • w) with hv
  have hMv : M • v = e i' • w := by
    rw [hv, ← Nat.cast_smul_eq_nsmul F, smul_smul, mul_inv_cancel₀ hM0, one_smul]
  have hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (e b) = e i' := by
    simp only [e, _root_.GlobalTheory.AdLat.sg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [AlgEquiv.coe_algHom, hbc, hc]
  have hvL : v ∈ Lh := by
    refine (_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual v).1
      fun y hy => ?_
    set Y := _root_.GlobalTheory.AdLat.fv F y
    have hY : Y ∈ Lh := _root_.GlobalTheory.AdLat.Half.fv_mem_hat' (L : Set (Fin n → E)) y hy
    obtain ⟨y₂, hy₂, hY₂⟩ := hh b hb Y hY
    rw [hu] at hY₂
    have key : _root_.GlobalTheory.AdLat.hermA c G w Y =
        -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y) := by
      rw [hw, _root_.GlobalTheory.AdLat.Half.herm_sub_left, _root_.GlobalTheory.AdLat.Half.herm_sub_right, ← hg z Y]
      ring
    have h2 : e i' * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y) =
        algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂ := by
      rw [← hsg, ← _root_.GlobalTheory.AdLat.Half.herm_smul_right, hY₂, hnat,
        _root_.GlobalTheory.AdLat.Half.herm_smul_right, AlgHom.commutes]
    have h3 : _root_.GlobalTheory.AdLat.hermA c G v Y = -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂ := by
      rw [hv, algebra_compatible_smul (_root_.GlobalTheory.AdLat.RA F E),
        _root_.GlobalTheory.AdLat.Half.herm_smul_left, _root_.GlobalTheory.AdLat.Half.herm_smul_left, key, mul_neg,
        h2, mul_neg, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hM0, map_one, one_mul]
    rw [h3]
    exact neg_mem (hpair _ (hgL z hz) y₂ hy₂)
  refine ⟨y₁ + v, add_mem hy₁ hvL, ?_⟩
  calc w = e i • w + e i' • w := by rw [← add_smul, he1, one_smul]
    _ = M • (y₁ + v) := by rw [hwy₁, ← hMv, smul_add]

end GlobalTheory.AdLat
end

