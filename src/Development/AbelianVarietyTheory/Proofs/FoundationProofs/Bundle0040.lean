module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumEqZeroAddUnits
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.NormFormGauss

theorem card_eq_sq {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    Fintype.card k = (Finset.univ.filter (fun x : k => s x = x)).card ^ 2 := by
  let T : k →+ k := s.toAddMonoidHom - AddMonoidHom.id k
  have hT : ∀ x, T x = s x - x := fun x => rfl
  have h1 : Nat.card k = Nat.card (k ⧸ T.ker) * Nat.card T.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h2 : Nat.card (k ⧸ T.ker) = Nat.card T.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv
  have h3 : Nat.card T.ker = (Finset.univ.filter (fun x : k => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [AddMonoidHom.mem_ker, hT, sub_eq_zero]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have h4 : Nat.card T.range = Nat.card T.ker := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun u : T.ker => (⟨(s r - r) * u, ⟨r * u, ?_⟩⟩ : T.range)) ⟨?_, ?_⟩)
    · have hu : s u = u := by
        have := u.2
        rw [AddMonoidHom.mem_ker, hT, sub_eq_zero] at this
        exact this
      rw [hT, map_mul, hu]; ring
    · intro u v huv
      have := congrArg Subtype.val huv
      exact Subtype.ext (mul_left_cancel₀ hr this)
    · rintro ⟨_, t, rfl⟩
      refine ⟨⟨(s t - t) / (s r - r), ?_⟩, ?_⟩
      · rw [AddMonoidHom.mem_ker, hT, sub_eq_zero, map_div₀, hθ, map_sub, hs]
        field_simp
        ring
      · apply Subtype.ext
        simp only [hT]
        field_simp
  rw [← Nat.card_eq_fintype_card, h1, h2, h4, h3, sq]

theorem sum_norm_units {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    ∃ m : ℕ, Fintype.card kˣ = m * (Finset.univ.filter (fun x : kˣ => s x = x)).card ∧
      ∀ f : k → ℂ, ∑ x : kˣ, f (x * s x) =
        m * ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y := by
  let S : kˣ →* kˣ := Units.map s.toMonoidHom
  have hS : ∀ x : kˣ, ((S x : kˣ) : k) = s x := fun x => rfl
  let N : kˣ →* kˣ := MonoidHom.id _ * S
  let D : kˣ →* kˣ := MonoidHom.id _ / S
  have hN : ∀ x : kˣ, ((N x : kˣ) : k) = x * s x := fun x => rfl
  have hD : ∀ x : kˣ, ((D x : kˣ) : k) = x / s x := fun x => by
    simp [D, hS]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have hne : ∀ x : kˣ, s x ≠ 0 := fun x => by simp
  have hDk : ∀ x : kˣ, x ∈ D.ker ↔ s x = x := fun x => by
    rw [MonoidHom.mem_ker, Units.ext_iff, hD, Units.val_one, div_eq_one_iff_eq (hne x), eq_comm]
  have hker : N.ker = D.range := by
    ext x
    rw [MonoidHom.mem_ker, Units.ext_iff, hN, Units.val_one]
    constructor
    · intro hx
      by_cases h : (1 + x : k) = 0
      · refine ⟨Units.mk0 _ hr, Units.ext ?_⟩
        rw [hD, Units.val_mk0, hθ, div_neg, div_self hr]
        linear_combination -h
      · refine ⟨Units.mk0 _ h, Units.ext ?_⟩
        have h' := hne (Units.mk0 _ h)
        rw [hD, div_eq_iff h', Units.val_mk0, map_add (f := _), map_one]
        linear_combination -hx
    · rintro ⟨y, rfl⟩
      rw [hD, map_div₀, hs]
      have := hne y
      have := y.ne_zero
      field_simp
  have c1 : Nat.card kˣ = Nat.card N.range * Nat.card N.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange N).toEquiv]
  have c2 : Nat.card kˣ = Nat.card D.range * Nat.card D.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange D).toEquiv]
  have c3 : Nat.card N.range = Nat.card D.ker := by
    rw [← hker, c1, mul_comm] at c2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos c2
  have hle : N.range ≤ D.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hDk, hN, map_mul, hs, mul_comm]
  have hr' : N.range = D.ker := Subgroup.eq_of_le_of_card_ge hle c3.ge
  have c4 : Nat.card D.ker = (Finset.univ.filter (fun x : kˣ => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, hDk]
  refine ⟨Nat.card N.ker, ?_, fun f => ?_⟩
  · rw [← Nat.card_eq_fintype_card, c1, c3, c4, mul_comm]
  · have himg : Finset.univ.image N = Finset.univ.filter (fun x : kˣ => s x = x) := by
      ext x
      simp only [Finset.mem_filter, ← hDk, ← hr', Finset.mem_image, Finset.mem_univ, true_and]
      rfl
    have := Finset.sum_comp (s := Finset.univ) (fun y : kˣ => f y) N
    simp only [hN] at this
    rw [this, ← himg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [nsmul_eq_mul]
    congr 2
    have hy' : y ∈ Set.range N := by simpa using hy
    rw [MonoidHom.card_fiber_eq_of_mem_range N hy' (⟨1, map_one N⟩ : (1 : kˣ) ∈ Set.range N),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1

theorem sum_eq_zero_add_units {k : Type} [Field k] [Fintype k] {M : Type} [AddCommMonoid M]
    (g : k → M) : ∑ x : k, g x = g 0 + ∑ x : kˣ, g x := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]
  congr 1
  symm
  refine Finset.sum_bij (fun x _ => (x : k)) ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro a _ b _ h; exact Units.ext h
  · intro b hb
    exact ⟨Units.mk0 b (by simpa using hb), by simp, rfl⟩
  · intro a _; rfl

theorem gauss_field {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) (f : k → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b) (h0 : f 0 = 1)
    (u : k) (hu : s u = u) (hfu : f u ≠ 1) :
    ∑ x : k, f (x * s x) = -(Real.sqrt (Fintype.card k) : ℂ) := by
  obtain ⟨m, hm, hsum⟩ := sum_norm_units s hs r hr
  have hq := card_eq_sq s hs r hr
  set q := (Finset.univ.filter (fun x : k => s x = x)).card with hqdef
  set a := (Finset.univ.filter (fun x : kˣ => s x = x)).card with hadef
  have hqa : q = 1 + a := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then (1 : ℕ) else 0)
    rw [hqdef, hadef, Finset.card_filter, Finset.card_filter, this, if_pos (map_zero s)]
  have ha : 0 < a := Finset.card_pos.2 ⟨1, by simp⟩
  have hcard : Fintype.card k = 1 + Fintype.card kˣ := by
    have := sum_eq_zero_add_units (fun _ : k => (1 : ℕ))
    simpa using this
  have hmq : m = q + 1 := by
    apply Nat.eq_of_mul_eq_mul_right ha
    rw [hm, hq, hqa] at hcard
    rw [hqa]
    nlinarith
  have hz : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
    have h1 : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f (u + y) =
        ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y := by
      refine Finset.sum_equiv (Equiv.addLeft u) ?_ ?_
      · intro i; simp [hu]
      · intro i _; rfl
    simp only [hadd, ← Finset.mul_sum] at h1
    have h2 : (f u - 1) * ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
      linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hfu)
  have hu1 : ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y = -1 := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then f x else 0)
    rw [← Finset.sum_filter, hz, ← Finset.sum_filter] at this
    simp only [map_zero, if_true, h0] at this
    linear_combination -this
  rw [sum_eq_zero_add_units, hsum, hu1, hq, hmq]
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg q)]
  simp [h0]

theorem gauss_quotient : ∀ {R : Type} [CommRing R] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r ∈ P, σ r ∈ P) → (∃ r, σ r - r ∉ P) → ∀ χ : R → ℂ, (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → (∀ r ∈ P, χ r = 1) → (∀ t, χ (σ t) = χ t) → (∃ t, χ t ≠ 1) → (∑ᶠ q : R ⧸ P, χ (w * (Quotient.out q : R) * σ (Quotient.out q : R))) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) := by
  intro R _ σ w hσ hw P hP hfin hst ⟨r, hr⟩ χ hadd h0 hχP hχσ ⟨t, ht⟩
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ (fun r hr => hst r hr)
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x) := fun x => rfl
  have hout : ∀ q : R ⧸ P, Ideal.Quotient.mk P (Quotient.out q) = q := fun q => Quotient.out_eq q
  have hcongr : ∀ a b : R, Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → χ a = χ b := by
    intro a b h
    have h1 := hχP _ (Ideal.Quotient.eq.1 h)
    have h2 := hadd (a - b) b
    rw [h1, one_mul, sub_add_cancel] at h2
    exact h2
  let f : R ⧸ P → ℂ := fun q => χ (w * Quotient.out q)
  have hf : ∀ a : R, f (Ideal.Quotient.mk P a) = χ (w * a) := fun a =>
    hcongr _ _ (by rw [map_mul, map_mul, hout])
  have key := gauss_field s
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, hσ])
    (Ideal.Quotient.mk P r)
    (by
      rw [hs, ← map_sub]
      exact fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h))
    f
    (fun a b => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← map_add (f := _), hf, hf, hf, mul_add, hadd])
    (by rw [← map_zero (Ideal.Quotient.mk P), hf, mul_zero, h0])
    (Ideal.Quotient.mk P (t + σ t))
    (by rw [hs, map_add σ, hσ, add_comm])
    (by
      rw [hf, mul_add, hadd, ← hχσ (w * σ t), map_mul, hσ, ← hadd, ← add_mul, hw, one_mul]
      exact ht)
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, ← key]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_rhs => rw [← hout q]
  rw [hs, ← map_mul, hf, mul_assoc]

end GlobalTheory.NormFormGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankOfFrame
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

def frameMap (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ)
    (hF : ∀ j, IsMF Γ (w j) (F j)) :
    (Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) →ₗ[ℂ] ModularForm Γ k where
  toFun g := (IsMF.sum (f := fun j => ⇑(g j) * F j) Finset.univ
    (fun j _ => ((isMF_coe_top (g j)).mono le_top).mul (hF j) (by ring))).toMF
  map_add' g h := by
    ext τ
    simp [add_mul, Finset.sum_add_distrib, Finset.sum_apply]
  map_smul' c g := by
    ext τ
    simp [Finset.mul_sum, mul_assoc, Finset.sum_apply]

theorem frameMap_apply (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)
    (k : ℤ) (hF : ∀ j, IsMF Γ (w j) (F j)) (g : Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) :
    ⇑(frameMap Γ w F k hF g) = ∑ j, ⇑(g j) * F j := rfl

theorem mul_slash_levelOne {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ)
    (g : Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) (j : Fin r) (x : SL(2, ℤ)) :
    (⇑(g j) * F j) ∣[k] x = ⇑(g j) * (F j ∣[w j] x) := by
  have h := ModularForm.mul_slash_SL2 (k - w j) (w j) x (⇑(g j)) (F j)
  rw [sub_add_cancel] at h
  rw [h, IsMF.slash_top (isMF_coe_top (g j)) x]

theorem frameMap_injective (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (s : Fin r → SL(2, ℤ))
    (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ) (hF : ∀ j, IsMF Γ (w j) (F j))
    (hdet : ∀ τ, (evM s w F τ).det ≠ 0) : Function.Injective (frameMap Γ w F k hF) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  have hsum : ∑ j, ⇑(g j) * F j = 0 := by
    rw [← frameMap_apply Γ w F k hF g, hg]
    rfl
  have hrow : ∀ i τ, ∑ j, (g j) τ * (F j ∣[w j] s i) τ = 0 := by
    intro i τ
    have h1 : (∑ j, ⇑(g j) * F j) ∣[k] s i = 0 := by
      rw [hsum]
      exact SlashAction.zero_slash _ _
    rw [SlashAction.sum_slash] at h1
    simp only [mul_slash_levelOne w F k g _ (s i)] at h1
    have h2 := congrFun h1 τ
    simpa [Finset.sum_apply] using h2
  have hv : ∀ τ, (fun j => (g j) τ) = 0 := by
    intro τ
    apply Matrix.eq_zero_of_mulVec_eq_zero (hdet τ)
    funext i
    simp only [Matrix.mulVec, dotProduct, evM, Matrix.of_apply, Pi.zero_apply]
    rw [← hrow i τ]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  funext j
  ext τ
  exact congrFun (hv τ) j

theorem finrank_sum_le_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (ModularForm Γ k) →
    (∀ j, IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) →
    ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (ModularForm Γ k) := by
  intro Γ r s w F k hΓ hfin hF hdet
  have hinj := frameMap_injective Γ s w F k hF hdet
  have : Module.Finite ℂ (Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) :=
    Module.Finite.of_injective (frameMap Γ w F k hF) hinj
  have : ∀ j, Module.Finite ℂ (ModularForm 𝒮ℒ (k - w j)) := fun j =>
    Module.Finite.of_surjective (LinearMap.proj (R := ℂ)
      (φ := fun j : Fin r => ModularForm 𝒮ℒ (k - w j)) j)
      (fun y => ⟨Pi.single j y, by simp⟩)
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_injective hinj

end GlobalTheory.OddFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
section
noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma quotient_mk_eq_mk_iff_sub_mem (A B : Submodule R X) (x y : B.toAddSubgroup) :
    ((x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = y) ↔
      (y : X) - x ∈ A := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp [neg_add_eq_sub]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma heis_apply_eq_of_sub_mem_of_fixes {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A B : Submodule R X}
    (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : y - x ∈ A) : W y v = W x v := by
  have hyx : y - x ∈ B := B.sub_mem hy hx
  calc W y v = W (x + (y - x)) v := by rw [add_sub_cancel]
    _ = W x (W (y - x) v) := (h.comp_of_mem hB hx hyx v).symm
    _ = W x v := by rw [hv _ hxy]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma quotient_out_sub_mem (A B : Submodule R X)
    (q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) (x : B.toAddSubgroup)
    (hq : (x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = q) :
    ((Quotient.out q : B.toAddSubgroup) : X) - x ∈ A := by
  rw [← quotient_mk_eq_mk_iff_sub_mem, hq]
  exact (QuotientAddGroup.out_eq' q).symm

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
theorem _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (A B : Submodule R X) (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) (v : M)
    (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) (ι : Type) [Fintype ι] (f : ι → X)
    (hf : ∀ i, f i ∈ B) (ht : ∀ b ∈ B, ∃! i, b - f i ∈ A) :
    _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
      _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι := by
  let φ : ι → B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    fun i => ((⟨f i, hf i⟩ : B.toAddSubgroup) : B.toAddSubgroup ⧸ _)
  have hφ : Function.Bijective φ := by
    constructor
    · intro i j hij
      have hji : f j - f i ∈ A := (quotient_mk_eq_mk_iff_sub_mem A B _ _).1 hij
      obtain ⟨k, -, hk⟩ := ht (f j) (hf j)
      rw [hk i hji, hk j (by simp)]
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H b =>
        obtain ⟨i, hi, -⟩ := ht b b.2
        exact ⟨i, (quotient_mk_eq_mk_iff_sub_mem A B _ _).2 hi⟩
  let e := Equiv.ofBijective φ hφ
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.FinWeil.sumOp
    rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact heis_apply_eq_of_sub_mem_of_fixes h hB hv (hf i) (Quotient.out (e i)).2
      (quotient_out_sub_mem A B (e i) ⟨f i, hf i⟩ rfl)
  · unfold _root_.GlobalTheory.FinWeil.idx
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_congr e, Nat.card_eq_fintype_card]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
theorem _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero (A B : Submodule R X)
    (hi : _root_.GlobalTheory.FinWeil.idx A B ≠ 0) :
    ∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A := by
  unfold _root_.GlobalTheory.FinWeil.idx at hi
  rw [AddSubgroup.relIndex, AddSubgroup.index] at hi
  haveI := Nat.finite_of_card_ne_zero hi
  let e := Finite.equivFin (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)
  refine ⟨_, fun i => ((Quotient.out (e.symm i) : B.toAddSubgroup) : X),
    fun i => (Quotient.out (e.symm i) : B.toAddSubgroup).2, ?_⟩
  intro b hb
  refine ⟨e (⟨b, hb⟩ : B.toAddSubgroup), ?_, fun j hj => ?_⟩
  · have := quotient_out_sub_mem A B (e.symm (e (⟨b, hb⟩ : B.toAddSubgroup))) ⟨b, hb⟩ (by simp)
    simpa using A.neg_mem this
  · have h1 : ((⟨b, hb⟩ : B.toAddSubgroup) :
        B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = e.symm j := by
      rw [← QuotientAddGroup.out_eq' (e.symm j), quotient_mk_eq_mk_iff_sub_mem]
      simpa using A.neg_mem hj
    rw [h1, Equiv.apply_symm_apply]

end

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma fixes_sumOp_of_selfDual {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A B : Submodule R X}
    (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) :
    _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v) := by
  intro b hb
  unfold _root_.GlobalTheory.FinWeil.sumOp
  set g : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup → M :=
    fun q => W ((Quotient.out q : B.toAddSubgroup) : X) v with hg
  have hinj : ∀ u : M, W b u = 0 → u = 0 := by
    intro u hu
    have h1 := h.neg_comp b u
    rw [hu, map_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _)
  have hmap : W b (∑ᶠ q, g q) = ∑ᶠ q, W b (g q) := by
    by_cases hs : (Function.support g).Finite
    · exact map_finsum (W b) hs
    · have hs' : ¬ (Function.support fun q => W b (g q)).Finite := by
        refine fun hfin => hs (hfin.subset fun q hq => ?_)
        exact fun h0 => hq (hinj _ h0)
      rw [finsum_of_infinite_support hs, map_zero, finsum_of_infinite_support hs']
  rw [hmap]
  let c : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    ((⟨b, hb⟩ : B.toAddSubgroup) : B.toAddSubgroup ⧸ _)
  have hterm : ∀ q, W b (g q) = g (c + q) := by
    intro q
    have hq : ((Quotient.out q : B.toAddSubgroup) : X) ∈ B := (Quotient.out q).2
    rw [hg, h.comp_of_mem hB hb hq v]
    refine (heis_apply_eq_of_sub_mem_of_fixes h hB hv (B.add_mem hb hq) (Quotient.out (c + q)).2
      (quotient_out_sub_mem A B (c + q) (⟨b, hb⟩ + Quotient.out q) ?_)).symm
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  simp_rw [hterm]
  exact finsum_comp_equiv (Equiv.addLeft c)

open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.sumOp_transversal : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M},
    _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X),
    _root_.GlobalTheory.FinWeil.SelfDual γ B → (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → ∀ (ι : Type) [Fintype ι]
      (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) →
      _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
        _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι) ∧
    (_root_.GlobalTheory.FinWeil.idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧
      ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧
      (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v)) ∧
      ∀ (c : ℂ) v, _root_.GlobalTheory.FinWeil.sumOp W A B (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A B v) ∧
    (B ≤ A → _root_.GlobalTheory.FinWeil.idx A B = 1 ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W A B v = v) := by
  intro R X M _ _ _ _ _ σ w γ W h A B hB
  have hunit : ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → B ≤ A →
      _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ _i : Unit, W 0 v ∧
        _root_.GlobalTheory.FinWeil.idx A B = Fintype.card Unit := fun v hv hBA =>
    _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h A B hB v hv Unit (fun _ => 0) (fun _ => B.zero_mem)
      (fun b hb => ⟨(), by simpa using hBA hb, fun _ _ => rfl⟩)
  refine ⟨fun v hv ι _ f hf ht => _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h A B hB v hv ι f hf ht,
    fun hi => ⟨_root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A B hi,
      fun v hv => fixes_sumOp_of_selfDual h hB hv, fun c v => ?_⟩, fun hBA => ?_⟩
  · unfold _root_.GlobalTheory.FinWeil.sumOp
    simp_rw [map_smul]
    exact (smul_finsum c _).symm
  · refine ⟨(hunit 0 (fun a _ => map_zero _) hBA).2.trans (by simp), fun v hv => ?_⟩
    rw [(hunit v hv hBA).1]
    simpa using hv 0 A.zero_mem

end GlobalTheory.FinWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaMemRange
section
open Polynomial

namespace GlobalTheory.KummerCob

theorem zeta_mem_range : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Field Ω] [Algebra K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → ζ ∈ Set.range (algebraMap K Ω) := by
  intro k K Ω _ _ _ _ _ _ _ N ζ hN hζ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : k) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  let φ : k →+* Ω := (algebraMap K Ω).comp ((algebraMap k[X] K).comp Polynomial.C)
  have hφ : Function.Injective φ := φ.injective
  have hξ' : IsPrimitiveRoot (φ ξ) N := hξ.map_of_injective hφ
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine ⟨(algebraMap k[X] K (Polynomial.C ξ)) ^ i, ?_⟩
  rw [map_pow, ← hi]
  rfl

end GlobalTheory.KummerCob
end

