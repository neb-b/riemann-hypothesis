module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLattices
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DualCompletion

open Formalism.L2.G.RelativeIndexFlags

theorem hform_mulVec_left {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A)
    (t x : Fin n → A) : hform τ J (B *ᵥ t) x = ∑ a, τ (t a) * ((cT τ B * J) *ᵥ x) a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

theorem hform_col {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A)
    (a : Fin n) (c : A) (x : Fin n → A) :
    hform τ J (B *ᵥ Pi.single a c) x = τ c * ((cT τ B * J) *ᵥ x) a := by
  rw [hform_mulVec_left, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, zero_mul]
  · intro h; exact (h (Finset.mem_univ a)).elim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J Λ ↔ y ∈ dualSet σ J Λ := by
  refine ⟨fun hy => ?_, fun hy => Submodule.subset_span hy⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => intro x _; simp [hform]
  | add y z _ _ hy hz =>
    intro x hx
    have : hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
      simp [hform, mul_add, Finset.sum_add_distrib]
    rw [this]; exact add_mem (hy x hx) (hz x hx)
  | smul a y _ hy =>
    intro x hx
    have : hform σ J x (a • y) = algebraMap (𝓞 E) E a * hform σ J x y := by
      simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]; exact mul_mem ⟨a, rfl⟩ (hy x hx)

theorem exists_common_den {p : ℕ} (hp : p.Prime) (M : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG) (B : GL (Fin n) E)
    (hB : IsLocBasis p (M : Set (Fin n → E)) B) :
    ∃ s : ℕ, ¬ p ∣ s ∧ ∀ m ∈ M, ∀ a, (s : E) * ((B⁻¹).1 *ᵥ m) a ∈ (algebraMap (𝓞 E) E).range := by
  classical
  have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.1 h)
  obtain ⟨S, rfl⟩ := hM
  choose s hs H using fun m : S => (hB m.1).1 ⟨1, h1, by
    rw [Nat.cast_one, one_smul]; exact Submodule.subset_span m.2⟩
  refine ⟨∏ m, s m, fun hd => ?_, fun m hm => ?_⟩
  · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
    exact hs a ha
  · induction hm using Submodule.span_induction with
    | mem y hy =>
      intro a
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ ⟨y, hy⟩), mul_comm (s _), Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) (H ⟨y, hy⟩ a)
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [Matrix.mulVec_add, Pi.add_apply, mul_add]; exact add_mem (hy a) (hz a)
    | smul c y _ hy =>
      intro a
      rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def, mul_left_comm]
      exact mul_mem ⟨c, rfl⟩ (hy a)

theorem isLocBasis_dual (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {p : ℕ} (hp : p.Prime)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG) (B : GL (Fin n) E)
    (hB : IsLocBasis p (M : Set (Fin n → E)) B) (C : GL (Fin n) E) (hC : C.1 = cT (σ : E →+* E) B.1 * J) :
    IsLocBasis p (dualL (σ : E →+* E) J M : Set (Fin n → E)) C⁻¹ := by
  classical
  have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.1 h)
  intro x
  rw [inv_inv, hC]
  simp only [SetLike.mem_coe, mem_dualL]
  constructor
  · rintro ⟨s, hs, hx⟩
    choose t ht H using fun a : Fin n => (hB (B.1 *ᵥ Pi.single a 1)).2 ⟨1, h1, fun b => by
      rw [Nat.cast_one, one_mul]; exact latB_col B a b⟩
    refine ⟨(∏ a, t a) * s, fun hd => ?_, fun a => ?_⟩
    · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
      · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
        exact ht a ha
      · exact hs hd
    · have h := hx _ (H a)
      rw [Formalism.UG.P.csDual_hform_smul_left, hform_col, map_one, one_mul, map_natCast, Matrix.mulVec_smul,
        Pi.smul_apply, smul_eq_mul] at h
      rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ a), mul_comm (t a), Nat.cast_mul, Nat.cast_mul,
        mul_assoc, mul_assoc]
      exact mul_mem (natCast_mem _ _) h
  · rintro ⟨s, hs, hx⟩
    obtain ⟨t, ht, H⟩ := exists_common_den hp M hM B hB
    refine ⟨t * s, fun hd => ((Nat.Prime.dvd_mul hp).1 hd).elim ht hs, fun m hm => ?_⟩
    have e : m = B.1 *ᵥ ((B⁻¹).1 *ᵥ m) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, hform_mulVec_left]
    refine sum_mem fun a _ => ?_
    obtain ⟨b, hb⟩ := H m hm a
    have h2 := sig_int σ b
    rw [hb, map_mul, map_natCast] at h2
    have h3 := mul_mem h2 (hx a)
    convert h3 using 1
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
    show σ _ * _ = _
    ring

theorem mem_latS_dualL (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M)
    (w : Fin n → E ⊗[F] v.adicCompletion F) :
    w ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J M) ↔
      ∀ u ∈ latS (F := F) (v.adicCompletion F) (intV E v) M,
        hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) u w ∈ intV E v := by
  classical
  haveI := v.isMaximal
  obtain ⟨p, -, -, hv, hp, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hB⟩ := LocB.exists_isLocBasis p E M hM.fg hM.span_eq_top
  have hu : IsUnit (cT (σ : E →+* E) B.1 * J).det := by
    rw [Matrix.det_mul, cT, Matrix.det_transpose]
    refine IsUnit.mul ?_ hJ
    have := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).map (σ : E →+* E)
    rwa [RingHom.map_det] at this
  let C : GL (Fin n) E := Matrix.GeneralLinearGroup.mk'' _ hu
  have hC : C.1 = cT (σ : E →+* E) B.1 * J := rfl
  have hD := isLocBasis_dual σ J hp M hM.fg B hB C hC
  rw [latS_of_locBasis v hp hv _ _ hD, latS_of_locBasis v hp hv _ _ hB, mem_latS_latB, map_inv, inv_inv]
  have hC' : (bc (inclE (F := F) (v.adicCompletion F)) C).1 =
      cT (sigR σ (v.adicCompletion F)) (bc (inclE (F := F) (v.adicCompletion F)) B).1 *
        J.map (inclE (F := F) (v.adicCompletion F)) := by
    show C.1.map (inclE (F := F) (v.adicCompletion F)) =
      cT (sigR σ (v.adicCompletion F)) (B.1.map (inclE (F := F) (v.adicCompletion F))) * _
    rw [hC, Matrix.map_mul]
    congr 1
  rw [hC']
  set B' := bc (inclE (F := F) (v.adicCompletion F)) B with hB'
  constructor
  · intro h u hu
    rw [mem_latS_latB] at hu
    have e : u = B'.1 *ᵥ ((B'⁻¹).1 *ᵥ u) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, hform_mulVec_left]
    exact sum_mem fun a _ => mul_mem (sigR_mem v σ (hu a)) (h a)
  · intro h a
    have h1 := h (B'.1 *ᵥ Pi.single a 1) (by
      rw [mem_latS_latB]
      intro b
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases hb : b = a
      · subst hb; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hb]; exact zero_mem _)
    rwa [hform_col, map_one, one_mul] at h1

theorem dual_move (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (L Lb : Submodule (𝓞 E) (Fin n → E))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : IsUnit J.det) (hL : Submodule.IsFullLattice E L)
    (hLb : Submodule.IsFullLattice E Lb) (hy : y ∈ UPts σ J (v.adicCompletion F))
    (hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb) :
    ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) := by
  have hyU : cT (sigR σ (v.adicCompletion F)) y.1 * J.map (inclE (F := F) (v.adicCompletion F)) * y.1 =
      J.map (inclE (F := F) (v.adicCompletion F)) := hy
  have key : ∀ z x : Fin n → E ⊗[F] v.adicCompletion F,
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z ((y⁻¹).1 *ᵥ x) =
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) (y.1 *ᵥ z) x := by
    intro z x
    have e := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
      y.1 z ((y⁻¹).1 *ᵥ x)
    rw [hyU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at e
    exact e.symm
  intro x
  rw [mem_latS_dualL σ J hJ v L hL, mem_latS_dualL σ J hJ v Lb hLb]
  refine ⟨fun H z hz => ?_, fun H z hz => ?_⟩
  · rw [key]
    refine H _ ((hyl _).2 ?_)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hz
  · have h1 := H _ ((hyl z).1 hz)
    rw [key, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1

end GlobalTheory.DualCompletion

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorMemAdelicForms
section
noncomputable section

namespace GlobalTheory.LevelHecke.UpKeeps

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

section Fr

variable {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E]

theorem atInf_mul_inv' (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

theorem atInf_inv_mul' (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * atInf emb (γ : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.inv_mul]
  simp

def trans (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) {G : ι → Matrix (Fin n) (Fin n) ℂ} (y : Frames G) : Frames G :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ, fun τ => by
    rw [det_mul]
    exact (Matrix.isUnit_det_of_right_inverse (atInf_mul_inv' emb γ τ)).mul (y.2 τ)⟩

theorem isTr_iff (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) {G : ι → Matrix (Fin n) (Fin n) ℂ} (y' y : Frames G) :
    IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) y' y ↔ y' = trans emb γ⁻¹ y := by
  constructor
  · intro h
    apply Subtype.ext
    funext τ
    show y'.1 τ = _ * y.1 τ
    rw [h τ, ← Matrix.mul_assoc, atInf_inv_mul', Matrix.one_mul]
  · rintro rfl τ
    show y.1 τ = _ * (_ * y.1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv', Matrix.one_mul]

def twist (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (G : ι → Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    (Frames G → ℂ) →+ (Frames G → ℂ) where
  toFun h := fun y => c * h (trans emb γ⁻¹ y)
  map_zero' := by funext y; simp
  map_add' a b := by funext y; simp [mul_add]

theorem twist_eq_zero (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (G : ι → Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : Frames G → ℂ) (h0 : twist emb γ G c h = 0) : h = 0 := by
  funext z
  have e : z = trans emb γ⁻¹ (trans emb γ z) := (isTr_iff emb γ _ _).1 fun _ => rfl
  have h1 : c * h (trans emb γ⁻¹ (trans emb γ z)) = 0 := congrFun h0 (trans emb γ z)
  rw [← e] at h1
  exact (mul_eq_zero.1 h1).resolve_left hc

end Fr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem atV_conj {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J} (h : AtV v η) (κ : GA σ J) : AtV v (κ * η * κ⁻¹) := by
  intro v' hv'
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, h v' hv', mul_one, mul_inv_cancel]

variable (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
  {k : Type} [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k)

theorem pair_move (hp : PMap S v hv p) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' κ : GA σ J)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (η : GA σ J) :
    p (x' * η) = (p (x * (κ * η))).act (glE γ) := by
  apply hp.1 γ hγ
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hx, mul_assoc, mul_assoc]

theorem valAt_move (hb : v ∉ bad) (hp : PMap S v hv p) (g : GA σ J → Frames (gramC J emb) → ℂ) (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' : GA σ J) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (q : Pr (𝓞 E) (Fin n → E) k) :
    valAt v p g x' (q.act (glE γ)) = twist emb γ (gramC J emb) (S.chi κ : ℂ) (valAt v p g x q) := by
  have hκ := (S.U_eq κ.1).1 κ.2
  let c : GA σ J := ⟨κ.1, hκ.1⟩
  have hcv : p (x * c) = p x := (hp.2.1 x c).2 (hκ.2 v)
  have hmv := pair_move S v hv p hp γ hγ x x' c hx
  have hU : ∀ z : GA σ J, p (z * c) = p z := fun z => (hp.2.1 z c).2 (hκ.2 v)
  unfold valAt
  by_cases h : ∃ η, AtV v η ∧ p (x * η) = q
  · have h' : ∃ η, AtV v η ∧ p (x' * η) = q.act (glE γ) := by
      obtain ⟨η, h1, h2⟩ := h
      refine ⟨c⁻¹ * η * c⁻¹⁻¹, atV_conj h1 _, ?_⟩
      rw [hmv, ← h2, ← hU (x * η)]
      congr 2
      group
    rw [dite_eq_left h, dite_eq_left h']
    obtain ⟨h1, h2⟩ := h.choose_spec
    obtain ⟨h1', h2'⟩ := h'.choose_spec
    generalize h.choose = η at h1 h2
    generalize h'.choose = η' at h1' h2'
    rw [hmv] at h2'
    have h3 := Pr.act_injective _ h2'
    have h4 : p (x * η * (η⁻¹ * c * η')) = p (x * η) := by
      rw [h2, ← h3]; congr 1; group
    have h5 := (hp.2.1 _ _).1 h4
    have hoff : ∀ v', v' ≠ v → bc (prV (E := E) v') (η⁻¹ * c * η' : GA σ J).1 = bc (prV (E := E) v') κ.1 := by
      intro v' hv'
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, h1 v' hv', h1' v' hv',
        inv_one, one_mul, mul_one]
    have hmem : (η⁻¹ * c * η' : GA σ J).1 ∈ S.U := by
      refine (S.U_eq _).2 ⟨(η⁻¹ * c * η' : GA σ J).2, fun v' => ?_⟩
      by_cases e : v' = v
      · subst e; exact h5
      · rw [hoff v' e]; exact hκ.2 v'
    have hchi : S.chi ⟨_, hmem⟩ = S.chi κ := by
      have := S.chi_triv (κ⁻¹ * ⟨_, hmem⟩) fun v' hv' => by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        show _ * bc (prV (E := E) v') (η⁻¹ * c * η' : GA σ J).1 = 1
        rw [hoff v' (fun e => hb (e ▸ hv')), inv_mul_cancel]
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    funext y
    have := hg γ hγ (x * η) (x' * η') ⟨_, hmem⟩ (by
      show (x' * η').1 = _ * (x * η).1 * (η⁻¹ * c * η' : GA σ J).1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hx]
      show _ = _ * _ * (_ * κ.1 * _)
      group) y (trans emb γ⁻¹ y) ((isTr_iff emb γ _ _).2 rfl)
    rw [this, hchi]
    rfl
  · have h' : ¬ ∃ η, AtV v η ∧ p (x' * η) = q.act (glE γ) := by
      rintro ⟨η, h1, h2⟩
      rw [hmv] at h2
      have h3 := Pr.act_injective _ h2
      refine h ⟨c * η * c⁻¹, atV_conj h1 _, ?_⟩
      rw [← h3, ← hU (x * (c * η * c⁻¹))]
      congr 1
      group
    rw [dite_eq_right h, dite_eq_right h', map_zero]

theorem upAd_mem_adForms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E) (lam : ι → DomWeight n), ∀ g ∈ AdForms S emb lam, upAd res t v p g ∈ AdForms S emb lam := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hp res t lam g hg
  refine ⟨?_, fun x _ => ?_⟩
  · intro γ hγ x x' κ hx y y' hy
    have hκ := (S.U_eq κ.1).1 κ.2
    have hpx : p x' = (p x).act (glE γ) := by
      have := pair_move S v hv p hp γ hγ x x' ⟨κ.1, hκ.1⟩ hx 1
      rwa [mul_one, mul_one, (hp.2.1 x ⟨κ.1, hκ.1⟩).2 (hκ.2 v)] at this
    have key : upAd res t v p g x' = twist emb γ (gramC J emb) (S.chi κ : ℂ) (upAd res t v p g x) := by
      have hz := twist_eq_zero emb γ (gramC J emb) (S.chi κ : ℂ) (Units.ne_zero _)
      unfold upAd
      rw [AddMonoidHom.map_finsum_of_preimage_zero _ hz]
      simp only [AddMonoidHom.map_finsum_of_preimage_zero _ hz]
      symm
      refine finsum_mem_eq_of_bijOn (Pr.act (glE γ)) ⟨fun q hq => ?_, (Pr.act_injective _).injOn, fun q hq => ?_⟩ fun q _ => ?_
      · rw [hpx]; exact Pr.Inc.act hq _
      · have e : (q.act (glE γ).symm).act (glE γ) = q := by
          rw [Pr.act_act, LinearEquiv.symm_trans_self, Pr.act_refl]
        refine ⟨q.act (glE γ).symm, ?_, e⟩
        rw [hpx, ← e] at hq
        exact (Pr.inc_act_iff _ _ _).1 hq
      · exact (valAt_move S emb v hv p hb hp g hg.1 γ hγ x x' κ hx q).symm
    rw [key, (isTr_iff emb γ _ _).1 hy]
    rfl
  · have hval : ∀ q, valAt v p g x q ∈ ValC (gramC J emb) lam := by
      intro q
      unfold valAt
      split_ifs with h
      · exact hg.2 _ (Set.mem_univ _)
      · exact zero_mem _
    show upAd res t v p g x ∈ ValC (gramC J emb) lam
    unfold upAd
    refine finsum_induction (· ∈ ValC (gramC J emb) lam) (zero_mem _) (fun _ _ => add_mem) fun q => ?_
    exact finsum_induction (· ∈ ValC (gramC J emb) lam) (zero_mem _) (fun _ _ => add_mem) fun _ => hval q

end GlobalTheory.LevelHecke.UpKeeps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFormulaHaarOrbitStabilizer
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeWeil

theorem inner_eq {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [MulAction G X] (x₀ : X)
    (μ' : Measure (MulAction.stabilizer G x₀)) [μ'.IsMulLeftInvariant] (f : G → ℝ≥0∞) (a b : G)
    (hab : a • x₀ = b • x₀) :
    ∫⁻ h, f (a * (h : G)) ∂μ' = ∫⁻ h, f (b * (h : G)) ∂μ' := by
  have hc : b⁻¹ * a ∈ MulAction.stabilizer G x₀ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hab, inv_smul_smul]
  rw [← lintegral_mul_left_eq_self (μ := μ') (fun h => f (b * (h : G))) ⟨_, hc⟩]
  simp [← mul_assoc]

theorem weil_formula : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), ∀ (μ' : Measure (MulAction.stabilizer G x₀)) (ν : Measure X), μ'.IsHaarMeasure → IsFiniteMeasureOnCompacts ν → ν ≠ 0 → (∀ g : G, ν.map (fun y => g • y) = ν) → ν {y | ¬ ∃ g : G, g • x₀ = y} = 0 → ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s y * (h : G)) ∂μ' ∂ν := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀ μ' ν hμ' hνc hν0 hinv hnull
  obtain ⟨-, s₀, hs₀m, hs₀⟩ := GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section G X x₀
  have hcont : Continuous fun g : G => g • x₀ := continuous_id.smul continuous_const
  have hclosed : IsClosed ((MulAction.stabilizer G x₀ : Subgroup G) : Set G) :=
    isClosed_eq hcont continuous_const
  have hemb : IsClosedEmbedding (Subtype.val : MulAction.stabilizer G x₀ → G) :=
    hclosed.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace (MulAction.stabilizer G x₀) := hemb.locallyCompactSpace
  have : SecondCountableTopology (MulAction.stabilizer G x₀) :=
    hemb.isEmbedding.secondCountableTopology
  have : SigmaCompactSpace (MulAction.stabilizer G x₀) := inferInstance
  have : IsLocallyFiniteMeasure μ' := inferInstance
  have : SigmaFinite μ' := inferInstance
  have hae : ∀ᵐ y ∂ν, ∃ g : G, g • x₀ = y := hnull
  have hΦ : Measurable fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G) :=
    (hs₀m.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  set μ : Measure G := (ν.prod μ').map
    (fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G)) with hμ
  have key0 : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s₀ y * (h : G)) ∂μ' ∂ν := by
    intro f hf
    rw [hμ, lintegral_map hf hΦ]
    exact lintegral_prod _ (hf.comp hΦ).aemeasurable
  have hleft : μ.IsMulLeftInvariant := by
    refine ⟨fun g => Measure.ext_of_lintegral _ fun f hf => ?_⟩
    have hF : Measurable fun y => ∫⁻ h, f (s₀ y * (h : G)) ∂μ' :=
      (hf.comp hΦ).lintegral_prod_right'
    rw [lintegral_map hf (measurable_const_mul g), key0 (fun a => f (g * a)) (hf.comp (measurable_const_mul g)),
      key0 f hf]
    conv_rhs => rw [← hinv g, lintegral_map hF (continuous_const_smul g).measurable]
    refine lintegral_congr_ae (hae.mono fun y hy => ?_)
    have h2 : ∃ k : G, k • x₀ = g • y := by
      obtain ⟨k, rfl⟩ := hy
      exact ⟨g * k, mul_smul _ _ _⟩
    have := inner_eq x₀ μ' f (g * s₀ y) (s₀ (g • y)) (by rw [mul_smul, hs₀ y hy, hs₀ _ h2])
    simpa [mul_assoc] using this
  have hfin : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.measurableSet
    have hL : IsCompact ((fun g : G => g • x₀) '' K) := hK.image hcont
    have hM : IsCompact ((Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K)) :=
      hemb.isCompact_preimage (hK.inv.mul hK)
    rw [← lintegral_indicator_one hKm, key0 _ (measurable_one.indicator hKm)]
    calc _ ≤ ∫⁻ y, ((fun g : G => g • x₀) '' K).indicator
            (fun _ => μ' ((Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K))) y ∂ν := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          by_cases hyK : y ∈ (fun g : G => g • x₀) '' K
          · rw [Set.indicator_of_mem hyK]
            obtain ⟨k, hk, hky⟩ := hyK
            rw [inner_eq x₀ μ' _ (s₀ y) k (by rw [hs₀ y hy]; exact hky.symm),
              ← lintegral_indicator_one hM.measurableSet]
            refine lintegral_mono fun h => ?_
            by_cases hh : k * (h : G) ∈ K
            · have : h ∈ (Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K) :=
                ⟨k⁻¹, by simpa using hk, k * h, hh, by simp⟩
              simp [Set.indicator_of_mem hh, Set.indicator_of_mem this]
            · simp [Set.indicator_of_notMem hh]
          · rw [Set.indicator_of_notMem hyK]
            have : ∀ h : MulAction.stabilizer G x₀, s₀ y * (h : G) ∉ K := fun h hh =>
              hyK ⟨_, hh, by
                have h1 : (h : G) • x₀ = x₀ := h.2
                simp only [mul_smul, h1, hs₀ y hy]⟩
            simp [Set.indicator_of_notMem (this _)]
      _ < ⊤ := by
          rw [lintegral_indicator_const hL.measurableSet]
          exact ENNReal.mul_lt_top hM.measure_lt_top hL.measure_lt_top
  have hne : μ Set.univ ≠ 0 := by
    rw [← lintegral_one, key0 _ measurable_const]
    simp only [lintegral_const, one_mul]
    exact mul_ne_zero (isOpen_univ.measure_ne_zero μ' Set.univ_nonempty)
      (by simpa using hν0)
  obtain ⟨n, hn⟩ : ∃ n, μ (compactCovering G n) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← iUnion_compactCovering G]
    exact measure_iUnion_null hcon
  have hpos : μ.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering G n) hn
  refine ⟨μ, ⟨⟩, fun f hf s hs => ?_⟩
  rw [key0 f hf]
  exact lintegral_congr_ae (hae.mono fun y hy =>
    inner_eq x₀ μ' f _ _ (by rw [hs y hy, hs₀ y hy]))

end GlobalTheory.GaugeWeil
end

