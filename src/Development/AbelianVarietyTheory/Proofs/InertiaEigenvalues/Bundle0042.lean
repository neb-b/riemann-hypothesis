module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulLeftTransversal
section
namespace GlobalTheory.LeftTransversalSum

theorem sum_mul_left_transversal {G M : Type} [Group G] [AddCommMonoid M] (H N : Subgroup G)
    (S : Finset G) (hS : ∀ s ∈ S, s ∈ H) (huniq : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ N)
    (f : G → M) (hf : ∀ (g n : G), n ∈ N → f (g * n) = f g) :
    ∀ h ∈ H, ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  intro h hh
  have hex : ∀ s : G, ∃ t : G, s ∈ S → t ∈ S ∧ t⁻¹ * (h * s) ∈ N := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨t, ht, -⟩ := huniq _ (H.mul_mem hh (hS s hs))
      exact ⟨t, fun _ => ht⟩
    · exact ⟨s, fun h' => absurd h' hs⟩
  choose σ hσ using hex
  have uniq : ∀ x ∈ H, ∀ t ∈ S, ∀ t' ∈ S, t⁻¹ * x ∈ N → t'⁻¹ * x ∈ N → t = t' :=
    fun x hx t ht t' ht' h1 h2 => (huniq x hx).unique ⟨ht, h1⟩ ⟨ht', h2⟩
  refine Finset.sum_nbij σ (fun s hs => (hσ s hs).1) ?_ ?_ ?_
  · intro s hs s' hs' he
    have n1 := (hσ s hs).2
    have n2 := (hσ s' hs').2
    rw [← he] at n2
    have hss : s⁻¹ * s' ∈ N := by
      convert N.mul_mem (N.inv_mem n1) n2 using 1
      group
    exact uniq s' (hS s' hs') s hs s' hs' hss (by simp)
  · intro t ht
    obtain ⟨s, ⟨hs, hsN⟩, -⟩ := huniq (h⁻¹ * t) (H.mul_mem (H.inv_mem hh) (hS t ht))
    refine ⟨s, hs, ?_⟩
    refine uniq (h * s) (H.mul_mem hh (hS s hs)) _ (hσ s hs).1 t ht (hσ s hs).2 ?_
    convert N.inv_mem hsN using 1
    group
  · intro s hs
    have e := hf (σ s) ((σ s)⁻¹ * (h * s)) (hσ s hs).2
    rw [mul_inv_cancel_left] at e
    exact e

end GlobalTheory.LeftTransversalSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumTranslateEq
section
universe u_1 u_2

namespace GlobalTheory.TranslateSum

theorem sum_translate_eq {G : Type u_1} {M : Type u_2} [Group G] [AddCommMonoid M]
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (huniq : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (f : G → M)
    (hf : ∀ (g v : G), v ∈ H → v ∈ V → f (g * v) = f g) :
    ∀ h ∈ H, ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  intro h hh
  have hex : ∀ s ∈ S, ∃ t : G, t ∈ S ∧ t⁻¹ * (h * s) ∈ V := fun s hs =>
    (huniq (h * s) (H.mul_mem hh (hS s hs))).exists
  choose φ hφS hφV using hex
  refine Finset.sum_bij φ hφS ?_ ?_ ?_
  · intro s hs t ht hst
    have h1 : s⁻¹ * t ∈ V := by
      have := V.mul_mem (V.inv_mem (hφV s hs)) (hφV t ht)
      rw [hst] at this
      have e : ((φ t ht)⁻¹ * (h * s))⁻¹ * ((φ t ht)⁻¹ * (h * t)) = s⁻¹ * t := by group
      rwa [e] at this
    have h2 : t⁻¹ * t ∈ V := by
      rw [inv_mul_cancel]; exact V.one_mem
    exact (huniq t (hS t ht)).unique ⟨hs, h1⟩ ⟨ht, h2⟩
  · intro u hu
    obtain ⟨s, hs, hsV⟩ := (huniq (h⁻¹ * u) (H.mul_mem (H.inv_mem hh) (hS u hu))).exists
    refine ⟨s, hs, ?_⟩
    have h1 : u⁻¹ * (h * s) ∈ V := by
      have := V.inv_mem hsV
      have e : (s⁻¹ * (h⁻¹ * u))⁻¹ = u⁻¹ * (h * s) := by group
      rwa [e] at this
    exact (huniq (h * s) (H.mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφV s hs⟩ ⟨hu, h1⟩
  · intro s hs
    have hm : (φ s hs)⁻¹ * (h * s) ∈ H :=
      H.mul_mem (H.inv_mem (hS _ (hφS s hs))) (H.mul_mem hh (hS s hs))
    have := hf (φ s hs) _ hm (hφV s hs)
    rwa [mul_inv_cancel_left] at this

end GlobalTheory.TranslateSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableFinprodOfFiniteSupportEulerSum
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem summable_finprod_of_finite_support_euler : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v)
    (a : ∀ v, X v → ℝ) (s : ι → ℝ), (∀ v x, 0 ≤ a v x) → (∀ v, a v (x0 v) = 1) → Summable s →
    (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, a v x ≤ s v) →
    Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => ∏ᶠ v, a v (f.1 v)) := by
  intro ι _ X x0 a s ha h1 hs hC
  classical
  have hs0 : ∀ v, 0 ≤ s v := fun v => by simpa using hC v ∅ (Finset.notMem_empty _)
  refine summable_of_sum_le (c := Real.exp (∑' v, s v)) (fun f => finprod_nonneg fun v => ha v _) ?_
  intro u
  set S : Finset ι := u.biUnion (fun f => f.2.toFinset) with hSdef
  have hsub : ∀ f ∈ u, ∀ w, f.1 w ≠ x0 w → w ∈ S := by
    intro f hf w hw
    exact Finset.mem_biUnion.2 ⟨f, hf, by simpa using hw⟩
  have hval : ∀ f ∈ u, ∏ᶠ v, a v (f.1 v) = ∏ x ∈ S.attach, a x.1 (f.1 x.1) := by
    intro f hf
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
    · exact (Finset.prod_attach S (fun v => a v (f.1 v))).symm
    · intro w hw
      by_contra hwS
      apply hw
      have : f.1 w = x0 w := by
        by_contra hne; exact hwS (hsub f hf w hne)
      simp [this, h1]
  let C : ∀ v, Finset (X v) := fun v => u.image (fun f => f.1 v)
  let φ : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} → (∀ v ∈ S, X v) := fun f v _ => f.1 v
  have hφinj : Set.InjOn φ u := by
    intro f hf g hg hfg
    apply Subtype.ext
    funext w
    by_cases hw : w ∈ S
    · exact congrFun (congrFun hfg w) hw
    · have hf' : f.1 w = x0 w := by by_contra h; exact hw (hsub f hf w h)
      have hg' : g.1 w = x0 w := by by_contra h; exact hw (hsub g hg w h)
      rw [hf', hg']
  have step1 : ∑ f ∈ u, ∏ᶠ v, a v (f.1 v) = ∑ p ∈ u.image φ, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) := by
    rw [Finset.sum_image hφinj]
    exact Finset.sum_congr rfl hval
  have himg : u.image φ ⊆ S.pi C := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_pi.2 fun v hv => Finset.mem_image_of_mem _ hf
  have step2 : ∑ p ∈ u.image φ, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) ≤
      ∑ p ∈ S.pi C, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ => Finset.prod_nonneg fun x _ => ha _ _
  have hCv : ∀ v, ∑ x ∈ C v, a v x ≤ 1 + s v := by
    intro v
    calc ∑ x ∈ C v, a v x ≤ ∑ x ∈ insert (x0 v) ((C v).erase (x0 v)), a v x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.insert_erase_subset _ _) fun x _ _ => ha v x
      _ = 1 + ∑ x ∈ (C v).erase (x0 v), a v x := by
          rw [Finset.sum_insert (Finset.notMem_erase _ _), h1]
      _ ≤ 1 + s v := by gcongr; exact hC v _ (Finset.notMem_erase _ _)
  calc ∑ f ∈ u, ∏ᶠ v, a v (f.1 v) ≤ ∑ p ∈ S.pi C, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) := step1 ▸ step2
    _ = ∏ v ∈ S, ∑ x ∈ C v, a v x := (Finset.prod_sum S C a).symm
    _ ≤ ∏ v ∈ S, Real.exp (s v) := Finset.prod_le_prod₀ (fun v _ => Finset.sum_nonneg fun x _ => ha v x)
          fun v _ => (hCv v).trans (by linarith [Real.add_one_le_exp (s v)])
    _ = Real.exp (∑ v ∈ S, s v) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' v, s v) := Real.exp_le_exp.2 (hs.sum_le_tsum _ (fun v _ => hs0 v))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjectiveOfResidueOfCotangent
section
open IsLocalRing Matrix TensorProduct

namespace GlobalTheory.LocalSurj

theorem exists_sub_mem_map_pow_succ {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (n : ℕ) (a : A)
    (ha : a ∈ (m ^ n).map f) : ∃ x ∈ m ^ n, a - f x ∈ (m ^ (n + 1)).map f := by
  change a ∈ Ideal.span (f '' ((m ^ n : Ideal R) : Set R)) at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨x', hx2, hx2'⟩ := hz
    refine ⟨x + x', add_mem hx hx2, ?_⟩
    have : y + z - f (x + x') = (y - f x) + (z - f x') := by rw [map_add (f := _)]; ring
    rw [this]; exact add_mem hx' hx2'
  | smul c y _ hy =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨s, hs⟩ := hm c
    refine ⟨s * x, Ideal.mul_mem_left _ _ hx, ?_⟩
    have : c • y - f (s * x) = c * (y - f x) + (c - f s) * f x := by
      rw [smul_eq_mul, map_mul]; ring
    rw [this]
    refine add_mem (Ideal.mul_mem_left _ _ hx') ?_
    rw [pow_succ', Ideal.map_mul]
    exact Ideal.mul_mem_mul hs (Ideal.mem_map_of_mem f hx)

noncomputable def approx {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) :
    (n : ℕ) → {x : R // a - f x ∈ (m ^ n).map f}
  | 0 => ⟨0, by rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial⟩
  | n + 1 =>
    let p := approx f m hm a n
    let h := exists_sub_mem_map_pow_succ f m hm n _ p.2
    ⟨p.1 + h.choose, by
      have := h.choose_spec.2
      rwa [map_add, ← sub_sub]⟩

theorem approx_succ_sub {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) (n : ℕ) :
    (approx f m hm a (n + 1)).1 - (approx f m hm a n).1 ∈ m ^ n := by
  simp only [approx, add_sub_cancel_left]
  exact (exists_sub_mem_map_pow_succ f m hm n _ (approx f m hm a n).2).choose_spec.1

theorem approx_sub_mem {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) {k n : ℕ} (h : k ≤ n) :
    (approx f m hm a n).1 - (approx f m hm a k).1 ∈ m ^ k := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have e : (approx f m hm a (n + 1)).1 - (approx f m hm a k).1 =
        ((approx f m hm a (n + 1)).1 - (approx f m hm a n).1) +
        ((approx f m hm a n).1 - (approx f m hm a k).1) := by ring
    rw [e]
    exact add_mem (Ideal.pow_le_pow_right hkn (approx_succ_sub f m hm a n)) ih

theorem surjective_of_residue_of_cotangent (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : R →+* A)
    (hc : IsAdicComplete (maximalIdeal R) R) (hf : IsLocalHom f)
    (hres : ∀ z : A, ∃ r, z - f r ∈ maximalIdeal A)
    (hcot : maximalIdeal A ≤ (maximalIdeal R).map f ⊔ maximalIdeal A ^ 2) :
    Function.Surjective f := by
  set m := maximalIdeal R

  have hle : maximalIdeal A ≤ m.map f := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian _) ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · simpa [pow_two, Ideal.smul_eq_mul] using hcot
  have hm : ∀ z : A, ∃ r, z - f r ∈ m.map f := fun z =>
    (hres z).imp fun r hr => hle hr
  have hmap : m.map f ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit f x hx
  intro a

  obtain ⟨L, hL⟩ := hc.prec' (fun n => (approx f m hm a n).1) (fun {k n} h => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    exact approx_sub_mem f m hm a h)
  refine ⟨L, ?_⟩
  rw [eq_comm, ← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top,
    Ideal.mem_iInf]
  intro n
  have h1 := (approx f m hm a n).2
  have h2 := hL n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h2
  have e : a - f L = (a - f (approx f m hm a n).1) + f ((approx f m hm a n).1 - L) := by
    rw [map_sub]; ring
  rw [e]
  refine (Ideal.map_pow f m n ▸ Ideal.pow_right_mono hmap n) (add_mem h1 (Ideal.mem_map_of_mem f h2))

end GlobalTheory.LocalSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateWeightGraded
section
namespace GlobalTheory

theorem tate_weight_graded : ∀ {C σ Γ : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] (χ : Γ →* Cˣ),
    (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) →
    ∀ (w : σ → ℤ) (J : Submodule C (σ →₀ C)),
    (∀ g : Γ, ∀ φ ∈ J, ∃ ψ ∈ J, ∀ m, ψ m = ((χ g ^ w m : Cˣ) : C) * (g • φ m)) →
    ∀ φ ∈ J, ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J := by
  intro C σ Γ _ _ _ χ hT w J hJ
  classical
  suffices H : ∀ n, ∀ φ ∈ J, φ.support.card = n → ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J by
    intro φ hφ d; exact H _ φ hφ rfl d
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro φ hφ hn
  have IH : ∀ φ' ∈ J, φ'.support.card < n → ∀ d : ℤ, φ'.filter (fun m => w m = d) ∈ J :=
    fun φ' h1 h2 d => ih _ h2 φ' h1 rfl d
  by_cases h0 : φ = 0
  · subst h0; intro d; rw [Finsupp.filter_zero]; exact J.zero_mem
  obtain ⟨m0, hm0⟩ := Finsupp.support_nonempty_iff.mpr h0
  have hc : φ m0 ≠ 0 := Finsupp.mem_support_iff.mp hm0
  set c := φ m0 with hcdef
  set φ0 : σ →₀ C := c⁻¹ • φ with hφ0def
  have hφ0 : φ0 ∈ J := J.smul_mem _ hφ
  have hsupp0 : φ0.support = φ.support := Finsupp.support_smul_eq (inv_ne_zero hc)
  have h1 : φ0 m0 = 1 := by
    simp only [φ0, Finsupp.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hc
  have hφeq : φ = c • φ0 := by
    simp only [φ0, smul_smul, mul_inv_cancel₀ hc, one_smul]
  suffices H0 : ∀ d : ℤ, φ0.filter (fun m => w m = d) ∈ J by
    intro d; rw [hφeq, Finsupp.filter_smul]; exact J.smul_mem _ (H0 d)
  have hcard : φ0.support.card = n := by rw [hsupp0, hn]
  have hm0' : m0 ∈ φ0.support := by rw [Finsupp.mem_support_iff, h1]; exact one_ne_zero
  have hψ : ∀ g : Γ, ∃ ψ ∈ J, ∀ m, ψ m =
      ((χ g ^ (-w m0) : Cˣ) : C) * (((χ g ^ w m : Cˣ) : C) * (g • φ0 m)) - φ0 m := by
    intro g
    obtain ⟨ψ', hψ'J, hψ'⟩ := hJ g φ0 hφ0
    refine ⟨((χ g ^ (-w m0) : Cˣ) : C) • ψ' - φ0, J.sub_mem (J.smul_mem _ hψ'J) hφ0, fun m => ?_⟩
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hψ']
  choose ψ hψJ hψm using hψ
  have hψm0 : ∀ g, ψ g m0 = 0 := by
    intro g
    rw [hψm, h1, smul_one, mul_one, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, sub_self]
  have hψ0 : ∀ g m, φ0 m = 0 → ψ g m = 0 := by
    intro g m h; rw [hψm, h, smul_zero, mul_zero, mul_zero, sub_zero]
  have hψsupp : ∀ g, (ψ g).support ⊆ φ0.support.erase m0 := by
    intro g m hm
    rw [Finset.mem_erase, Finsupp.mem_support_iff]
    rw [Finsupp.mem_support_iff] at hm
    refine ⟨?_, fun h => hm (hψ0 g m h)⟩
    rintro rfl; exact hm (hψm0 g)
  have hlt : ∀ g, (ψ g).support.card < n := fun g =>
    lt_of_le_of_lt (Finset.card_le_card (hψsupp g)) (hcard ▸ Finset.card_erase_lt_of_mem hm0')
  by_cases hall : ∀ g, ψ g = 0
  · have hw : ∀ m, φ0 m ≠ 0 → w m = w m0 := by
      intro m hm
      by_contra hne
      apply hm
      refine hT (w m0 - w m) (sub_ne_zero.mpr (Ne.symm hne)) (φ0 m) (fun g => ?_)
      have e := hψm g m
      rw [hall g, Finsupp.zero_apply, eq_comm, sub_eq_zero] at e
      have hex : w m0 - w m + -w m0 + w m = 0 := by ring
      conv_rhs => rw [← e]
      rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add,
        hex, zpow_zero, Units.val_one, one_mul]
    intro d
    by_cases hd : w m0 = d
    · rw [(Finsupp.filter_eq_self_iff _ _).mpr (fun m hm => (hw m hm).trans hd)]; exact hφ0
    · rw [(Finsupp.filter_eq_zero_iff _ _).mpr (fun m hm => by
        by_contra h; exact hd ((hw m h).symm.trans hm))]
      exact J.zero_mem
  · push_neg at hall
    obtain ⟨g, hg⟩ := hall
    obtain ⟨m1, hm1⟩ := Finsupp.support_nonempty_iff.mpr hg
    have hm1' := Finset.mem_of_mem_erase (hψsupp g hm1)
    have hψm1 : ψ g m1 ≠ 0 := Finsupp.mem_support_iff.mp hm1
    set a := φ0 m1 / ψ g m1 with hadef
    set φ' : σ →₀ C := φ0 - a • ψ g with hφ'def
    have hφ'J : φ' ∈ J := J.sub_mem hφ0 (J.smul_mem _ (hψJ g))
    have hφ'supp : φ'.support ⊆ φ0.support.erase m1 := by
      intro m hm
      rw [Finset.mem_erase, Finsupp.mem_support_iff]
      rw [Finsupp.mem_support_iff] at hm
      refine ⟨?_, fun h => hm ?_⟩
      · rintro rfl; apply hm
        simp only [φ', a, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
          div_mul_cancel₀ _ hψm1, sub_self]
      · simp only [φ', Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, h, hψ0 g m h,
          mul_zero, sub_zero]
    have hlt' : φ'.support.card < n :=
      lt_of_le_of_lt (Finset.card_le_card hφ'supp) (hcard ▸ Finset.card_erase_lt_of_mem hm1')
    intro d
    have hdec : φ0 = φ' + a • ψ g := by simp only [φ', sub_add_cancel]
    rw [hdec, Finsupp.filter_add, Finsupp.filter_smul]
    exact J.add_mem (IH _ hφ'J hlt' d) (J.smul_mem _ (IH _ (hψJ g) (hlt g) d))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerDistinguishedRegularSequence
section
open scoped NNReal

namespace GlobalTheory

theorem teichmuller_dvd_of_dvd_natCast_mul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (hx : x ≠ 0) (a : WittVector l O)
    (h : WittVector.teichmuller l x ∣ ((l : ℕ) : WittVector l O) * a) :
    WittVector.teichmuller l x ∣ a := by
  obtain ⟨b, hb⟩ := h
  have h0 : (((l : ℕ) : WittVector l O) * a).coeff 0 = 0 := by
    rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [hb, WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] at h0
  have hb0 : b.coeff 0 = 0 := (mul_eq_zero.mp h0).resolve_left hx
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton] at hb0
  obtain ⟨c, rfl⟩ := hb0
  have hl : ((l : ℕ) : WittVector l O) ≠ 0 := WittVector.p_nonzero l O
  refine ⟨c, mul_left_cancel₀ hl ?_⟩
  rw [hb]; ring

theorem teichmuller_distinguished_regular : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O), x ≠ 0 → 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → ∀ (k : ℕ) (a : WittVector l O), (WittVector.teichmuller l x ^ k ∣ E' * a → WittVector.teichmuller l x ^ k ∣ a) ∧ (E' ∣ WittVector.teichmuller l x ^ k * a → E' ∣ a) := by
  intro l _ O _ _ _ _ x e w E' hx he hw hE
  have hT : WittVector.teichmuller l x ≠ 0 := by
    intro h
    apply hx
    rw [← WittVector.teichmuller_coeff_zero l x, h]
    simp
  have h1 : ∀ a : WittVector l O, WittVector.teichmuller l x ∣ E' * a →
      WittVector.teichmuller l x ∣ a := by
    intro a h
    rw [hE, add_mul] at h
    have h2 : WittVector.teichmuller l x ∣ WittVector.teichmuller l x ^ e * a :=
      (dvd_pow_self _ he.ne').mul_right a
    have h3 := (dvd_add_right h2).mp h
    rw [mul_assoc] at h3
    exact hw.dvd_mul_left.mp (teichmuller_dvd_of_dvd_natCast_mul l O x hx _ h3)
  have hk : ∀ (k : ℕ) (a : WittVector l O), WittVector.teichmuller l x ^ k ∣ E' * a →
      WittVector.teichmuller l x ^ k ∣ a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a h
      obtain ⟨c, rfl⟩ := h1 a ((dvd_pow_self _ k.succ_ne_zero).trans h)
      rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left hT] at h
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih c h)
  intro k a
  refine ⟨hk k a, ?_⟩
  rintro ⟨b, hb⟩
  obtain ⟨c, rfl⟩ := hk k b ⟨a, hb.symm⟩
  refine ⟨c, mul_left_cancel₀ (pow_ne_zero k hT) ?_⟩
  rw [hb]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoRatioBoxCountsProdOne
section
open Filter

namespace GlobalTheory

theorem ratio_box_counts_tendsto_one (r : ℕ) (c : Fin r → ℕ) (m : ℕ) :
    Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) /
      ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  have key : ∀ i, Tendsto (fun k : ℕ => ((2 * (k + m) * c i + 1 : ℕ) : ℝ) /
      ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    intro i
    rcases Nat.eq_zero_or_pos (c i) with h | h
    · simp [h]
    · have hc : (0:ℝ) < c i := by exact_mod_cast h
      have hden : Tendsto (fun k : ℕ => ((2 * k * c i + 1 : ℕ) : ℝ)) atTop atTop := by
        push_cast
        apply tendsto_atTop_add_const_right
        exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2)).atTop_mul_const hc
      have h0 : Tendsto (fun k : ℕ => (2 * m * c i : ℝ) / ((2 * k * c i + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hden
      have h1 := (tendsto_const_nhds (x := (1:ℝ))).add h0
      rw [add_zero] at h1
      refine h1.congr (fun k => ?_)
      have hpos : ((2 * k * c i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
  have h := tendsto_finsetProd (Finset.univ : Finset (Fin r)) (fun i _ => key i)
  simp only [Finset.prod_const_one] at h
  refine h.congr (fun k => ?_)
  rw [Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexOfRootQuadraticNegDisc
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem totallyComplex_of_root_quadratic_neg_disc :
    ∀ (K : Type) [Field K] [NumberField K] (x : K) (a b : ℤ), x ^ 2 + (a : K) * x + (b : K) = 0 →
    a ^ 2 < 4 * b → NumberField.IsTotallyComplex K := by
  intro K _ _ x a b hx hab
  refine ⟨fun v => ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  set φ : K →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal hv
  have h := congrArg φ hx
  simp only [map_add (f := _), map_mul, map_pow, map_intCast, map_zero] at h
  have hab' : ((a : ℝ)) ^ 2 < 4 * (b : ℝ) := by exact_mod_cast hab
  nlinarith [sq_nonneg (2 * φ x + (a : ℝ))]

end GlobalTheory
end

