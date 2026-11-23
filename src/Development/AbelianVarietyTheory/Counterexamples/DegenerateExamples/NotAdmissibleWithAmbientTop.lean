module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds

@[expose] public section

noncomputable section

namespace GlobalTheory.SeriesSupportTest

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Polynomial

def plHom (D : D7) (k : Fin 2) (v : D.nd.PlG k) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) →+* MonoidAlgebra ℂ (G0g D.nd) := by
  classical
  exact MonoidAlgebra.mapDomainRingHom ℂ
    (MonoidHom.mulSingle (fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩)

theorem atPlace_eq (D : D7) (k : Fin 2) (v : D.nd.PlG k) (a) : atPlace D k v a = plHom D k v a := rfl

theorem atPlace_central (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (ha : ∀ b, a * b = b * a) :
    atPlace D k v a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
  classical
  rw [Subalgebra.mem_center_iff, atPlace_eq]
  intro b
  set kv : (Σ k : Fin 2, D.nd.PlG k) := ⟨k, v⟩ with hkv
  have hof : ∀ h, plHom D k v (MonoidAlgebra.of ℂ _ h) =
      MonoidAlgebra.of ℂ (G0g D.nd) (Pi.mulSingle kv h) := by
    intro h
    simp [plHom, kv]
  have hcomm : ∀ g' : G0g D.nd, g' kv = 1 → ∀ y,
      Commute (MonoidAlgebra.of ℂ (G0g D.nd) g') (plHom D k v y) := by
    intro g' hg' y
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      rw [hof]
      show _ * _ = _ * _
      rw [← map_mul, ← map_mul]
      congr 1
      funext j
      by_cases hj : j = kv
      · subst hj
        simp [hg']
      · simp [Pi.mulSingle_eq_of_ne hj]
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact hx.add_right hy
    | smul r x hx =>
      have e : plHom D k v (r • x) = r • plHom D k v x := by
        simp only [plHom, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_smul]
      rw [e]
      exact hx.smul_right r
  induction b using MonoidAlgebra.induction_on with
  | of g =>
    have hg : g = (Pi.mulSingle kv (g kv) : G0g D.nd) * ((Pi.mulSingle kv (g kv) : G0g D.nd)⁻¹ * g) :=
      (mul_inv_cancel_left _ _).symm
    have h1 : ((Pi.mulSingle kv (g kv) : G0g D.nd)⁻¹ * g : G0g D.nd) kv = 1 := by simp
    have hc : Commute (MonoidAlgebra.of ℂ (G0g D.nd) g) (plHom D k v a) := by
      rw [hg, map_mul, ← hof]
      refine Commute.mul_left ?_ (hcomm _ h1 a)
      exact (Commute.map (ha (MonoidAlgebra.of ℂ _ (g kv))).symm (plHom D k v))
    exact hc.eq
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

section Dual

variable {K : Type} [Field K]

theorem deg_rev {q : K[X]} (h : q.coeff 0 ≠ 0) : q.reverse.natDegree = q.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr h), Nat.sub_zero]

theorem rev_rev {q : K[X]} (h : q.coeff 0 ≠ 0) : q.reverse.reverse = q := by
  show reflect q.reverse.natDegree q.reverse = q
  rw [deg_rev h]
  exact reflect_reflect

theorem coeff_of_dvd {q f : K[X]} (h : q ∣ f) (hf : f.coeff 0 ≠ 0) : q.coeff 0 ≠ 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [mul_coeff_zero] at hf
  exact left_ne_zero_of_mul hf

theorem rev_dvd {q f : K[X]} (h : q ∣ f) : q.reverse ∣ f.reverse := by
  obtain ⟨r, rfl⟩ := h
  rw [reverse_mul_of_domain]
  exact dvd_mul_right _ _

theorem unit_of_rev {q : K[X]} (h : q.coeff 0 ≠ 0) (hu : IsUnit q.reverse) : IsUnit q := by
  have hd : q.reverse.natDegree = 0 := natDegree_eq_of_degree_eq_some (isUnit_iff_degree_eq_zero.mp hu)
  rw [deg_rev h] at hd
  rw [eq_C_of_natDegree_eq_zero hd]
  exact isUnit_C.mpr (Ne.isUnit h)

def dl (f : K[X]) : K[X] := C (f.coeff 0)⁻¹ * f.reverse

theorem dl_lab {N : ℕ} {f : K[X]} (h : f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0) :
    (dl f).Monic ∧ (dl f).natDegree = N ∧ (dl f).coeff 0 = (f.coeff 0)⁻¹ := by
  obtain ⟨hm, hd, h0⟩ := h
  have hrd : f.reverse.natDegree = N := by rw [deg_rev h0, hd]
  have hlc : f.reverse.leadingCoeff = f.coeff 0 := by
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0]
  have hc0 : f.reverse.coeff 0 = 1 := by rw [coeff_zero_reverse, hm.leadingCoeff]
  refine ⟨?_, ?_, ?_⟩
  · show (C (f.coeff 0)⁻¹ * f.reverse).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, hlc, inv_mul_cancel₀ h0]
  · show (C (f.coeff 0)⁻¹ * f.reverse).natDegree = N
    rw [natDegree_C_mul (inv_ne_zero h0), hrd]
  · show (C (f.coeff 0)⁻¹ * f.reverse).coeff 0 = _
    rw [coeff_C_mul, hc0, mul_one]

theorem dl_dl {N : ℕ} {f : K[X]} (h : f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0) : dl (dl f) = f := by
  have h3 := (dl_lab h).2.2
  rw [show dl (dl f) = C ((dl f).coeff 0)⁻¹ * (dl f).reverse from rfl, h3, inv_inv,
    show dl f = C (f.coeff 0)⁻¹ * f.reverse from rfl, reverse_mul_of_domain, reverse_C,
    rev_rev h.2.2, ← mul_assoc, ← C_mul, mul_inv_cancel₀ h.2.2, C_1, one_mul]

theorem dvd_dl {q f : K[X]} (h : q ∣ f) : q.reverse ∣ dl f := by
  show q.reverse ∣ C (f.coeff 0)⁻¹ * f.reverse
  exact dvd_mul_of_dvd_right (rev_dvd h) _

theorem ptp_inv (l : ℕ) {L : Type} [Field L] (x : L) :
    Formalism.CyclotomicNorms.primeToPart l x⁻¹ = (Formalism.CyclotomicNorms.primeToPart l x)⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    have key : ∀ n : ℕ, (0 : L) ^ n = ((0 : L) ^ n)⁻¹ := fun n => by
      rcases n with _ | n <;> simp
    unfold Formalism.CyclotomicNorms.primeToPart
    rw [inv_zero]
    exact key _
  · have ho : orderOf x⁻¹ = orderOf x := by
      calc orderOf x⁻¹ = orderOf ((Units.mk0 x hx)⁻¹ : Lˣ) := by
            rw [← orderOf_units, Units.val_inv_eq_inv_val, Units.val_mk0]
        _ = orderOf (Units.mk0 x hx) := orderOf_inv _
        _ = orderOf x := by rw [← orderOf_units, Units.val_mk0]
    unfold Formalism.CyclotomicNorms.primeToPart
    rw [ho, inv_pow]

theorem root_dl {g : ℕ} [Fact g.Prime] {N : ℕ} {f : (ZMod g)[X]} (h : f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0)
    {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar (dl f)) : x⁻¹ ∈ Formalism.CyclotomicNorms.rootsBar f := by
  obtain ⟨hm, hd, h0⟩ := h
  have hdl := dl_lab ⟨hm, hd, h0⟩
  unfold Formalism.CyclotomicNorms.rootsBar at hx ⊢
  have hx2 : eval x ((dl f).map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) = 0 :=
    (mem_roots ((hdl.1.map _).ne_zero)).mp hx
  rw [eval_map] at hx2
  refine (mem_roots ((hm.map _).ne_zero)).mpr ?_
  show eval x⁻¹ (f.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) = 0
  rw [eval_map]
  have hx' : eval₂ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) x f.reverse = 0 := by
    rw [show dl f = C (f.coeff 0)⁻¹ * f.reverse from rfl, eval₂_mul, eval₂_C] at hx2
    exact (mul_eq_zero.mp hx2).resolve_left ((_root_.map_ne_zero _).mpr (inv_ne_zero h0))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [eval₂_at_zero, coeff_zero_reverse, hm.leadingCoeff, map_one] at hx'
    exact one_ne_zero hx'
  let _ := invertibleOfNonzero (inv_ne_zero hx0)
  rw [← eval₂_reverse_eq_zero_iff, invOf_eq_inv, inv_inv]
  exact hx'

private theorem irreducible_reverse_of_coeff_zero_ne_zero {q : K[X]} (h0 : q.coeff 0 ≠ 0) (hq : Irreducible q) :
    Irreducible q.reverse := by
  have hr0 : q.reverse.coeff 0 ≠ 0 := by
    rw [coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hq.ne_zero
  refine irreducible_iff.mpr ⟨fun hu => hq.not_isUnit (unit_of_rev h0 hu), fun a b hab => ?_⟩
  have e : q = a.reverse * b.reverse := by rw [← reverse_mul_of_domain, ← hab, rev_rev h0]
  rcases hq.isUnit_or_isUnit e with hu | hu
  · left
    exact unit_of_rev (coeff_of_dvd (by rw [hab]; exact dvd_mul_right a b) hr0) hu
  · right
    exact unit_of_rev (coeff_of_dvd (by rw [hab]; exact dvd_mul_left b a) hr0) hu

theorem good_dl {N g : ℕ} [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X]) (χ : PP → J → (ZMod g)ˣ)
    (h : Formalism.CyclotomicNorms.IsGood N g f χ) : Formalism.CyclotomicNorms.IsGood N g (fun v => dl (f v)) (fun v j => (χ v j)⁻¹) := by
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := h
  have hdl0 : ∀ v, (dl (f v)).coeff 0 ≠ 0 := fun v => by
    rw [(dl_lab (ha v)).2.2]
    exact inv_ne_zero (ha v).2.2
  refine ⟨fun v => ⟨(dl_lab (ha v)).1, (dl_lab (ha v)).2.1, hdl0 v⟩, fun v => ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq0 : q.coeff 0 ≠ 0 := coeff_of_dvd (dvd_trans (dvd_mul_right q q) hq) (hdl0 v)
    have h2 : q.reverse * q.reverse ∣ f v := by
      have := dvd_dl hq
      rwa [dl_dl (ha v), reverse_mul_of_domain] at this
    exact unit_of_rev hq0 (hb v _ h2)
  · intro ℓ hℓ hB v x hx y hy hxy
    have := hc ℓ hℓ hB v _ (root_dl (ha v) hx) _ (root_dl (ha v) hy) (by rw [ptp_inv, ptp_inv, hxy])
    exact inv_injective this
  · intro ℓ hℓ hg v j x hx heq
    apply hd ℓ hℓ hg v j _ (root_dl (ha v) hx)
    dsimp only at heq
    rw [ptp_inv, heq, Units.val_inv_eq_inv_val, map_inv₀, ptp_inv, inv_inv]
  · intro a ha1 ha2
    obtain ⟨v, hv⟩ := he a ha1 ha2
    refine ⟨v, fun ⟨q, hq, hqd⟩ => hv ⟨q.reverse, ?_, ?_⟩⟩
    · have := dvd_dl hq
      rwa [dl_dl (ha v)] at this
    · rw [deg_rev (coeff_of_dvd hq (hdl0 v)), hqd]
  · obtain ⟨v, q, hirr, hq, hp, h1, h2⟩ := hf
    have hq0 := coeff_of_dvd hq (ha v).2.2
    refine ⟨v, q.reverse, irreducible_reverse_of_coeff_zero_ne_zero hq0 hirr, dvd_dl hq, ?_⟩
    rw [deg_rev hq0]
    exact ⟨hp, h1, h2⟩

end Dual

def dualFun (D : D7) (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : (ZMod (D.host.g k))[X] :=
  open Classical in if IsLabel D k f then dualLab D k f else f

theorem label_dual (D : D7) (k : Fin 2) {f} (h : IsLabel D k f) : IsLabel D k (dualLab D k f) := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have h' := dl_lab (N := D.R.r) h
  show (dl f).Monic ∧ (dl f).natDegree = D.R.r ∧ (dl f).coeff 0 ≠ 0
  exact ⟨h'.1, h'.2.1, by rw [h'.2.2]; exact inv_ne_zero h.2.2⟩

theorem good_dualFun (D : D7) (t : Tup2 D) (h : D.ntypes.goodTuple t) :
    D.ntypes.goodTuple (fun k v => dualFun D k (t k v)) := by
  unfold NTypes.goodTuple at h ⊢
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2⟩ := h k
  have e : (fun v => dualFun D k (t k v)) = fun v => dl (t k v) := by
    funext v
    unfold dualFun
    rw [if_pos (show IsLabel D k (t k v) from h1.1 v)]
    rfl
  show Formalism.CyclotomicNorms.IsGood _ _ (fun v => dualFun D k (t k v)) _ ∧
    Formalism.CyclotomicNorms.IsGood _ _ (fun v => dualFun D k (t k v)) _
  rw [e]
  exact ⟨by simpa only [inv_inv] using good_dl _ _ h2, good_dl _ _ h1⟩

end GlobalTheory.SeriesSupportTest
