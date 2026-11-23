module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartFrameProperties
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology

variable {K : UQ} (B : InvAlg K)

theorem eta_c (x : K.E) : K.eta (K.c x) = K.eta x := by
  unfold UQ.eta; rw [UnramNorm.val_c]

theorem norm_sigma (u : B.A) : Algebra.norm K.E (B.σ u) = K.c (Algebra.norm K.E u) := by
  have h := Algebra.norm_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) u
  rw [h, RingEquiv.apply_symm_apply]

theorem norm_ne_zero_of_isUnit {u : B.A} (hu : IsUnit u) : Algebra.norm K.E u ≠ 0 :=
  (hu.map (Algebra.norm K.E)).ne_zero

theorem eta_norm_mul_sigma {v : B.A} (hv : IsUnit v) : K.eta (Algebra.norm K.E (v * B.σ v)) = 1 := by
  rw [map_mul, norm_sigma, eta_mul (norm_ne_zero_of_isUnit B hv)
    ((map_ne_zero K.c).2 (norm_ne_zero_of_isUnit B hv)), eta_c, eta_sq]

theorem twist_mul {E : B.A} (hE : E * E = E) (x y : B.A) :
    (x * E + (1 - E)) * (y * E + (1 - E)) = x * y * E + (1 - E) := by
  linear_combination (x * y - x - y + 1) * hE

theorem twist_isUnit {E : B.A} (hE : E * E = E) {x : B.A} (hx : IsUnit x) : IsUnit (x * E + (1 - E)) := by
  obtain ⟨u, rfl⟩ := hx
  refine isUnit_iff_exists_inv.2 ⟨((u⁻¹ : B.Aˣ) : B.A) * E + (1 - E), ?_⟩
  rw [twist_mul B hE, Units.mul_inv, one_mul]; ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem e_mul_eS {e : ι → B.A} (he : OrthogonalIdempotents e) (i : ι) (I : Finset ι) :
    e i * eS B e I = if i ∈ I then e i else 0 := by
  unfold eS; rw [Finset.mul_sum]; split_ifs with h
  · rw [Finset.sum_eq_single i (fun j _ hji => he.ortho (Ne.symm hji)) (fun h' => absurd h h'), (he.idem i).eq]
  · exact Finset.sum_eq_zero fun j hj => he.ortho (fun hij => h (hij ▸ hj))

theorem eS_idem {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) :
    eS B e I * eS B e I = eS B e I := by
  show (∑ i ∈ I, e i) * eS B e I = _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [e_mul_eS B he, if_pos hi]

theorem sigma_e {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (i : ι) : B.σ (e i) = e i := by
  obtain ⟨f, -, -, -, h1, h2⟩ := h.2 i
  by_cases hi : i ∈ S
  · rw [(h1 hi).1, (h1 hi).2]
  · rw [(h2 hi).2, map_add (f := _), B.σ_σ, add_comm]

theorem sigma_eS {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (I : Finset ι) : B.σ (eS B e I) = eS B e I := by
  unfold eS; rw [map_sum]; exact Finset.sum_congr rfl fun i _ => sigma_e B h i

theorem chi_mul {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) {x y : B.A} (hx : IsUnit x)
    (hy : IsUnit y) : chi B e I (x * y) = chi B e I x * chi B e I y := by
  unfold chi
  have hE := eS_idem B he I
  rw [← twist_mul B hE, map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hx))
    (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy))]

theorem chi_norm {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (I : Finset ι) {w : B.A} (hw : IsUnit w) :
    chi B e I (w * B.σ w) = 1 := by
  unfold chi
  have hE := eS_idem B h.1.toOrthogonalIdempotents I
  have hσ : B.σ (w * eS B e I + (1 - eS B e I)) = B.σ w * eS B e I + (1 - eS B e I) := by
    rw [map_add (f := _), map_mul, map_sub, map_one, sigma_eS B h]
  rw [← twist_mul B hE, ← hσ]
  exact eta_norm_mul_sigma B (twist_isUnit B hE hw)

theorem eta_prod {s : Finset ι} (x : ι → K.E) (hx : ∀ i ∈ s, x i ≠ 0) :
    K.eta (∏ i ∈ s, x i) = ∏ i ∈ s, K.eta (x i) := by
  induction s using Finset.induction_on with
  | empty => simp [UQ.eta, val]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      eta_mul (hx a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

theorem chi_prod {e π : ι → B.A} {S : Finset ι} (h : IsFrame B e π S) (I J : Finset ι) (hJ : J ⊆ S) :
    chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card := by
  have he := h.1.1.toOrthogonalIdempotents
  set E := eS B e I with hEdef
  have hE := eS_idem B he I

  have h1 : (∏ j ∈ J.filter (· ∉ I), π j) * E = E := by
    refine Finset.prod_induction _ (fun t => t * E = E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : E = (1 - e j) * E := by
      rw [sub_mul, one_mul, mul_comm (e j) E, hEdef, mul_comm, e_mul_eS B he, if_neg hjI, sub_zero]
    show π j * E = E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have h2 : (∏ j ∈ J.filter (· ∈ I), π j) * (1 - E) = 1 - E := by
    refine Finset.prod_induction _ (fun t => t * (1 - E) = 1 - E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : 1 - E = (1 - e j) * (1 - E) := by
      have := e_mul_eS B he j I
      rw [if_pos hjI] at this
      rw [← hEdef] at this
      linear_combination -this
    show π j * (1 - E) = 1 - E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have hprod : (∏ j ∈ J, π j) * E + (1 - E) = ∏ j ∈ J.filter (· ∈ I), π j := by
    rw [← Finset.prod_filter_mul_prod_filter_not J (· ∈ I), mul_assoc]
    rw [h1]
    linear_combination -h2
  unfold chi
  rw [← hEdef, hprod, map_prod, eta_prod]
  · rw [Finset.filter_mem_eq_inter]
    rw [Finset.prod_congr rfl fun j hj => (h.2 j (hJ (Finset.mem_inter.1 hj).1)).2.2, Finset.prod_const]
  · intro j hj
    exact norm_ne_zero_of_isUnit B (h.2 j (hJ (Finset.mem_filter.1 hj).1)).1.1

theorem mul_eq_zero_of_idem {e : ι → B.A} (he : OrthogonalIdempotents e) {i j : ι} (hij : i ≠ j) {a b : B.A}
    (ha : a * e i = a) (hb : b * e j = b) : a * b = 0 := by
  rw [← ha, ← hb, show a * e i * (b * e j) = a * b * (e i * e j) by ring, he.ortho hij, mul_zero]

theorem sum_mul_sum_diag {e : ι → B.A} (he : OrthogonalIdempotents e) (s : Finset ι) (a b : ι → B.A)
    (ha : ∀ i ∈ s, a i * e i = a i) (hb : ∀ i ∈ s, b i * e i = b i) :
    (∑ i ∈ s, a i) * (∑ j ∈ s, b j) = ∑ i ∈ s, a i * b i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact Finset.sum_eq_single i (fun j hj hji => mul_eq_zero_of_idem B he (Ne.symm hji) (ha i hi) (hb j hj))
    (fun h => absurd hi h)

theorem chi_plus {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) {y : B.A} (hy : B.Plus y) :
    chi B e S y = K.eta (Algebra.norm K.E y) := by
  have he := h.1.toOrthogonalIdempotents
  have hcomp := h.1.complete
  choose f hf using h.2
  set E := eS B e S with hEdef
  have hE : E * E = E := eS_idem B he S
  have hσE : B.σ E = E := sigma_eS B h S
  have hfe : ∀ i ∈ Sᶜ, f i * e i = f i := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, hid.eq, (h2 hiS).1, add_zero]
  have hge : ∀ i ∈ Sᶜ, B.σ (f i) * e i = B.σ (f i) := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, mul_comm (B.σ (f i)) (f i), (h2 hiS).1, zero_add, ← map_mul, hid.eq]
  set F := ∑ i ∈ Sᶜ, f i with hFdef
  set G := ∑ i ∈ Sᶜ, B.σ (f i) with hGdef
  have hGσ : G = B.σ F := by rw [hGdef, hFdef, map_sum]
  have hFF : F * F = F := by
    rw [hFdef, sum_mul_sum_diag B he _ f f hfe hfe]; exact Finset.sum_congr rfl fun i _ => (hf i).1.eq
  have hFG : F * G = 0 := by
    rw [hFdef, hGdef, sum_mul_sum_diag B he _ f _ hfe hge]
    exact Finset.sum_eq_zero fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).1
  have hGG : G * G = G := by rw [hGσ, ← map_mul, hFF]
  have hFE : F * E = 0 := by
    rw [hFdef, hEdef, eS, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
      mul_eq_zero_of_idem B he (fun hij => Finset.mem_compl.1 hi (by rw [hij]; exact hj)) (hfe i hi) (he.idem j).eq
  have hGE : G * E = 0 := by rw [hGσ, ← hσE, ← map_mul, hFE, map_zero]
  have hFGsum : F + G = 1 - E := by
    have h1 : F + G = ∑ i ∈ Sᶜ, e i := by
      rw [hFdef, hGdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).2.symm
    rw [h1, ← hcomp, ← Finset.sum_add_sum_compl S e, hEdef, eS]; ring
  set w := y * F + G + E with hwdef
  have hσw : B.σ w = y * G + F + E := by
    rw [hwdef, map_add (f := _), map_add (f := _), map_mul, hy.2, hσE, hGσ, B.σ_σ]
  have hw : w * B.σ w = y * (1 - E) + E := by
    rw [hσw, ← hFGsum]
    linear_combination (y ^ 2 + 1) * hFG + y * hFF + (y + 1) * hFE + y * hGG + (y + 1) * hGE + hE
  have hE' : (1 - E) * (1 - E) = 1 - E := by linear_combination hE
  have hwwU : IsUnit (w * B.σ w) := by
    have := twist_isUnit B hE' hy.1
    rwa [sub_sub_cancel, ← hw] at this
  have hwU : IsUnit w := isUnit_of_mul_isUnit_left hwwU
  have hsplit : y = (y * E + (1 - E)) * (w * B.σ w) := by
    rw [hw]; linear_combination (y ^ 2 - 2 * y + 1) * hE
  unfold chi
  rw [← hEdef]
  conv_rhs => rw [hsplit]
  rw [map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy.1)) (norm_ne_zero_of_isUnit B hwwU),
    eta_norm_mul_sigma B hwU, mul_one]

theorem chi_frame_props : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), IsFrame B e π S →
    (∀ (I : Finset ι) (x y : B.A), IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y) ∧
    (∀ (I : Finset ι) (w : B.A), IsUnit w → chi B e I (w * B.σ w) = 1) ∧
    (∀ I J : Finset ι, I ⊆ S → J ⊆ S → chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card) ∧
    (∀ y, B.Plus y → chi B e S y = K.eta (Algebra.norm K.E y)) := by
  intro K B ι _ _ e π S h
  exact ⟨fun I x y hx hy => chi_mul B h.1.1.toOrthogonalIdempotents I hx hy, fun I w hw => chi_norm B h.1 I hw,
    fun I J _ hJ => chi_prod B h I J hJ, fun y hy => chi_plus B h.1 hy⟩

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartProdInl
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

theorem norm_prod_mk_one {K : UQ} (B₁ B₂ : InvAlg K) (y : B₁.A) :
    Algebra.norm K.E ((y, 1) : B₁.A × B₂.A) = Algebra.norm K.E y := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul K.E (B₁.A × B₂.A) (y, 1) =
      LinearMap.prodMap (Algebra.lmul K.E B₁.A y) (Algebra.lmul K.E B₂.A 1) := by
    ext z <;> simp
  rw [h, LinearMap.det_prodMap, map_one, map_one, mul_one]

theorem chi_prod_inl : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ : ι₁ → B₁.A) (e₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (x : B₁.A × B₂.A), chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) x = chi B₁ e₁ S₁ x.1 := by
  intro K B₁ B₂ ι₁ ι₂ e₁ e₂ S₁ x
  have hS : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
      (S₁.map Function.Embedding.inl) = ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) := by
    unfold eS
    rw [Finset.sum_map]
    show (∑ i ∈ S₁, ((e₁ i, 0) : B₁.A × B₂.A)) = ((∑ i ∈ S₁, e₁ i, 0) : B₁.A × B₂.A)
    rw [Prod.ext_iff]
    simp [Prod.fst_sum, Prod.snd_sum]
  unfold chi
  rw [hS]
  have hx : (x * ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) + (1 - ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A)) : B₁.A × B₂.A) =
      ((x.1 * eS B₁ e₁ S₁ + (1 - eS B₁ e₁ S₁), 1) : B₁.A × B₂.A) := by
    ext <;> simp
  change K.eta (Algebra.norm K.E (x * ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) + (1 - ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A)))) = _
  rw [hx, norm_prod_mk_one]

end GlobalTheory.UnitLemma.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OntoOCAdditivePoly
section
open Polynomial

theorem GlobalTheory.onto_OC_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by
  intro l hl E N a hNE ha haN b hb
  set f : ℂ_[l][X] := (∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k)) - C b with hf
  have hl1 : 1 < l := hl.out.one_lt
  have hinj : Function.Injective (fun k : ℕ => l ^ k) := Nat.pow_right_injective hl.out.two_le
  have hcoeff : ∀ j, f.coeff j = (∑ k ∈ Finset.range (E + 1), if l ^ k = j then a k else 0) - (if j = 0 then b else 0) := by
    intro j
    simp only [hf, coeff_sub, finsetSum_coeff, coeff_monomial, coeff_C, Finsupp.single_apply]
  have hcN : f.coeff (l ^ N) = a N := by
    rw [hcoeff]
    have h0 : l ^ N ≠ 0 := pow_ne_zero _ (by omega)
    rw [if_neg h0, sub_zero, Finset.sum_eq_single N]
    · simp
    · intro k _ hk; rw [if_neg]; intro h; exact hk (hinj h)
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hbound : ∀ j, ‖f.coeff j‖ ≤ 1 := by
    intro j
    rw [hcoeff]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro k hk
      split_ifs
      · exact ha k (by have := Finset.mem_range.1 hk; omega)
      · simp
    · rw [norm_neg]; split_ifs
      · exact hb
      · simp
  have hne : f.coeff (l ^ N) ≠ 0 := by
    rw [hcN]; intro h; rw [h, norm_zero] at haN; exact zero_ne_one haN
  have key := (_root_.GlobalTheory.card_roots_le_radius_bounds ℂ_[l] f 1 (l ^ N) zero_lt_one hne).1 (by
    intro j; simp only [one_pow, mul_one]; rw [hcN, haN]; exact hbound j)
  have hpos : 0 < Multiset.card (f.roots.filter fun z => ‖z‖ ≤ 1) :=
    lt_of_lt_of_le (pow_pos (by omega) N) key
  obtain ⟨W, hW⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  rw [Multiset.mem_filter] at hW
  obtain ⟨hr, hWn⟩ := hW
  refine ⟨W, hWn, ?_⟩
  have hroot := (mem_roots'.1 hr).2
  rw [IsRoot, hf, eval_sub, eval_finsetSum, eval_C] at hroot
  simp only [eval_monomial] at hroot
  exact sub_eq_zero.1 hroot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzVanishOffTranslates
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem parahoric_schwartz_vanish_off_translates : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) (N : ℕ), (∀ x, Φ x ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K)) → (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → (∀ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 → ∀ (lift : GL (Fin r) (IsLocalRing.ResidueField O) → Matrix (Fin r) (Fin r) O), (∀ g, (lift g).map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O))) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, ∑ᶠ g ∈ {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v}, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = 0) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ x ≠ 0 → ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ Φ N hsupp h2 h3 x hx
  classical
  by_contra hnot
  obtain ⟨z, hz⟩ := hsupp x hx
  have hc0 : algebraMap O K (ϖ ^ N) ≠ 0 := by
    rw [Ne, (IsFractionRing.injective O K).eq_iff' (map_zero _)]
    exact pow_ne_zero _ hϖ.ne_zero
  have hzn : ¬ ∃ (g : GL (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), z.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) := by
    rintro ⟨g, w, hw⟩
    apply hnot
    refine ⟨Units.mk0 _ hc0 • g, w, ?_⟩
    rw [← hw, ← hz]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨a, ha, hcore⟩ := _root_.GlobalTheory.gen_type_core O K r t ϖ hϖ z hzn
  have hsurj : ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), ∃ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) := by
    intro g
    have hs' : ∀ i j, ∃ o : O, IsLocalRing.residue O o = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) i j :=
      fun i j => IsLocalRing.residue_surjective _
    choose L hL using hs'
    exact ⟨Matrix.of L, by ext i j; exact hL i j⟩
  choose lift hlift using hsurj
  have hs := h3 a ha lift hlift x
  set G := {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v} with hG
  have hfix : ∀ g ∈ G, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = Φ x := by
    intro g hg
    obtain ⟨h, hh1, hh2, hh3⟩ := hcore g hg (lift g) (hlift g)
    rw [← h2 h hh1 hh2]
    congr 1
    have e1 := congrArg (fun m : Matrix (Fin r ⊕ Fin t) (Fin r) O => m.map (algebraMap O K)) hh3
    simp only [Matrix.map_mul] at e1
    rw [← hz] at e1
    rw [Matrix.mul_smul, Matrix.mul_smul] at e1
    exact smul_right_injective _ hc0 e1
  rw [finsum_mem_congr rfl hfix] at hs
  have hGfin : G.Finite := Set.toFinite G
  rw [finsum_mem_eq_finite_toFinset_sum _ hGfin, Finset.sum_const] at hs
  have h1 : (1 : GL (Fin r) (IsLocalRing.ResidueField O)) ∈ hGfin.toFinset := by
    rw [Set.Finite.mem_toFinset]; intro v _; simp
  have hcard : hGfin.toFinset.card ≠ 0 := Finset.card_ne_zero.2 ⟨_, h1⟩
  rw [nsmul_eq_mul] at hs
  exact hx ((mul_eq_zero.1 hs).resolve_left (by exact_mod_cast hcard))

theorem parahoric_schwartz_mem_span_translates : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ, (∃ N : ℕ, (∀ x (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), Φ (x + (ϖ ^ N • z).map (algebraMap O K)) = Φ x) ∧ ∀ x, Φ x ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K)) → (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → (∀ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 → ∀ (lift : GL (Fin r) (IsLocalRing.ResidueField O) → Matrix (Fin r) (Fin r) O), (∀ g, (lift g).map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O))) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, ∑ᶠ g ∈ {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v}, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = 0) → Φ ∈ Submodule.span ℂ {Ψ | ∃ g : GL (Fin r) K, Ψ = Set.indicator {x : Matrix (Fin r ⊕ Fin t) (Fin r) K | ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, x * (g : Matrix (Fin r) (Fin r) K) = (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) + ϖ • z).map (algebraMap O K)} (fun _ => (1 : ℂ))} := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ Φ ⟨N, hinv, hsupp⟩ h2 h3
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices O K r t ϖ hϖ N
  have hΩ := GlobalTheory.parahoric_schwartz_vanish_off_translates O K r t ϖ hϖ Φ N hsupp h2 h3
  set S : GL (Fin r) K → Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) := fun g =>
    {x | ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)} with hS
  have hconst : ∀ g x x', x ∈ S g → x' ∈ S g → Φ x = Φ x' := by
    rintro g x x' ⟨z, hz⟩ ⟨z', hz'⟩
    rw [_root_.GlobalTheory.invariant_const_on_translate O K r t ϖ hϖ Φ h2 x g z hz, _root_.GlobalTheory.invariant_const_on_translate O K r t ϖ hϖ Φ h2 x' g z' hz']
  have huniq : ∀ g g' x, x ∈ S g → x ∈ S g' → S g = S g' := by
    rintro g g' x ⟨z, hz⟩ ⟨z', hz'⟩
    ext y; constructor
    · rintro ⟨w, hw⟩; exact _root_.GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset O K r t ϖ hϖ x g g' z z' hz hz' y w hw
    · rintro ⟨w, hw⟩; exact _root_.GlobalTheory.ParahoricTranslate.translate_lattice_coset_subset O K r t ϖ hϖ x g' g z' z hz' hz y w hw
  let gs : Matrix (Fin r ⊕ Fin t) (Fin r) K → GL (Fin r) K := fun y =>
    if h : Φ y ≠ 0 then (hΩ y h).choose else 1
  have hgs : ∀ y, Φ y ≠ 0 → y ∈ S (gs y) := by
    intro y hy
    simp only [gs, dif_pos hy]
    exact (hΩ y hy).choose_spec
  let F : Finset (Set (Matrix (Fin r ⊕ Fin t) (Fin r) K)) :=
    (T.filter (fun y => Φ y ≠ 0)).image (fun y => S (gs y))
  have hcover : ∀ x, Φ x ≠ 0 → ∃ A ∈ F, x ∈ A := by
    intro x hx
    obtain ⟨z, hz⟩ := hsupp x hx
    obtain ⟨y, hyT, z', rfl⟩ := hT x z hz
    have hy : Φ y ≠ 0 := by rwa [hinv] at hx
    refine ⟨S (gs y), Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hyT, hy⟩, rfl⟩, ?_⟩
    obtain ⟨z₀, hz₀⟩ := hgs y hy
    exact GlobalTheory.T.lattice_coset_translate_mem_of_cover O K r t ϖ hϖ N y (gs y) z₀ hz₀ (fun z => hΩ _ (by rwa [hinv])) z'
  have hF : ∀ A ∈ F, ∃ g, A = S g := by
    intro A hA
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hA
    exact ⟨_, rfl⟩
  let c : Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) → ℂ := fun A => if h : A.Nonempty then Φ h.some else 0
  have hc : ∀ A ∈ F, ∀ x ∈ A, c A = Φ x := by
    intro A hA x hx
    obtain ⟨g, rfl⟩ := hF A hA
    have hne : (S g).Nonempty := ⟨x, hx⟩
    simp only [c, dif_pos hne]
    exact hconst g _ _ hne.some_mem hx
  have heq : Φ = ∑ A ∈ F, c A • A.indicator (fun _ => (1 : ℂ)) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Set.indicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hx : Φ x = 0
    · rw [hx]; symm
      apply Finset.sum_eq_zero
      intro A hA
      split_ifs with h
      · rw [hc A hA x h, hx]
      · rfl
    · obtain ⟨A, hA, hxA⟩ := hcover x hx
      rw [Finset.sum_eq_single A]
      · rw [if_pos hxA, hc A hA x hxA]
      · intro B hB hBA
        rw [if_neg]
        intro hxB
        obtain ⟨g, rfl⟩ := hF A hA
        obtain ⟨g', rfl⟩ := hF B hB
        exact hBA (huniq g' g x hxB hxA)
      · intro h; exact absurd hA h
  rw [heq]
  refine Submodule.sum_mem _ fun A hA => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  obtain ⟨g, rfl⟩ := hF A hA
  exact ⟨g, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaModuleSaturationTheoremStatement
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phiGammaModule_saturation_theorem :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W]
      (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → W →ₗ[k⸨X⸩] V),
      (∀ i, Function.Injective (f i)) →
      (∀ i x, f i (D'.φ i x) = D.φ i (f (i - 1) x)) →
      (∀ i x, f i (D'.γ i x) = D.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        let N' := fun i => (N i).comap ((f i).restrictScalars k⟦X⟧);
        (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC
  refine ⟨fun i => Sat.isLat_comap _ (hf i) (hN i), fun i => ?_, fun i x hx => ?_⟩
  · have h := Sat.comap_pull D D' i (f (i - 1)) (f i) (hf _) (hf _) (hφ i) (hN (i - 1)).1
    rw [← h, ← Sat.comap_sh, ← Sat.comap_sh]
    exact ⟨Submodule.comap_mono (hAB i).1, Submodule.comap_mono (hAB i).2⟩
  · rw [← Sat.comap_sh]
    change f i _ ∈ sh 1 (N i)
    rw [map_sub, hγ]
    exact hC i _ hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilTorusMulUnipotentCommute
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem NL_smul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (s : A.K) (y : A.L) :
    A.NL (s • y) = s ^ 2 * A.NL y := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_eq_succ hU.finrank_eq
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hU.finrank_eq
  have hp := ((Algebra.IsPushout.comm F E A.K A.L).1 A.push).out
  let c := hp.basis b
  unfold Et.NL
  rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap_of_basis c, Fintype.card_fin]

theorem mOp_nOp : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (z : A.K) (φ : A.L → ℂ),
      mOp A ω s (nOp A ψ x z φ) = nOp A ψ x ((s : A.K) ^ 2 * z) (mOp A ω s φ) := by
  intro F E _ _ _ _ _ A ψ x μ ω _ s z φ
  funext y
  simp only [mOp, nOp, NL_smul]
  rw [show (z * (x : A.K) * ((s : A.K) ^ 2 * A.NL y)) = (s : A.K) ^ 2 * z * x * A.NL y by ring]
  ring

end GlobalTheory.JR.WeilQuad
end
end

