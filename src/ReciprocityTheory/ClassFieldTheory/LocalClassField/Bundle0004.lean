module

public import Mathlib
public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
public import ReciprocityTheory.GroupCohomology.PartialProdCoe
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.IsTwoCocycleCoboundary
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

section Alg

variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)

def IsTwoCocycle (c : G → G → A) : Prop := ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0

def D1 (y : G → A) (g h : G) : A := ρ g (y h) - y (g * h) + y g

variable {ρ}

variable {N} {c : G → G → A} (hc : IsTwoCocycle ρ c)
  {r s : G → G} (hrs : ∀ g, r g * s g = g) (hr : ∀ g, r g ∈ N)
  (hrn : ∀ n ∈ N, ∀ g, r (n * g) = n * r g) (hsn : ∀ n ∈ N, ∀ g, s (n * g) = s g)

include hrs hr in
theorem s_mem {n : G} (hn : n ∈ N) : s n ∈ N := by
  have h : s n = (r n)⁻¹ * n := by rw [eq_inv_mul_iff_mul_eq, hrs]
  rw [h]; exact N.mul_mem (N.inv_mem (hr n)) hn


include hc hrs hr hrn hsn in
theorem stepA (h0 : ∀ n ∈ N, ∀ m ∈ N, c n m = 0) (n : G) (hn : n ∈ N) (g : G) :
    c n g - D1 ρ (fun x => - c (r x) (s x)) n g = 0 := by
  have h1 := hc n (r g) (s g)
  rw [hrs, h0 n hn _ (hr g)] at h1
  simp only [D1]
  rw [hrn n hn, hsn n hn, h0 _ (hr n) _ (s_mem hrs hr hn), map_neg]
  linear_combination (norm := abel) h1

include hc in
theorem mul_left_of_zero (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (n : G) (hn : n ∈ N) (g h : G) :
    c (n * g) h = ρ n (c g h) := by
  have h1 := hc n g h
  rw [h0 n hn, h0 n hn] at h1
  linear_combination (norm := abel) - h1

include hc in
theorem theta_mul [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (g m : G) (hm : m ∈ N) (k : G) :
    c g (m * k) = c g m + ρ (g * m * g⁻¹) (c g k) := by
  have h1 := hc g m k
  have h2 := mul_left_of_zero hc h0 (g * m * g⁻¹) (‹N.Normal›.conj_mem m hm g) g k
  rw [inv_mul_cancel_right] at h2
  rw [h0 m hm, map_zero, h2] at h1
  linear_combination (norm := abel) h1


include hc hrs hr hrn hsn in
theorem stepB [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (e : G → A) (he0 : ∀ g ∈ N, e g = 0)
    (he : ∀ g, ∀ n ∈ N, c g (g⁻¹ * n * g) = e g - ρ n (e g)) (n : G) (hn : n ∈ N) (g : G) :
    c n g - D1 ρ (fun x => ρ (r x) (e (s x))) n g = 0 ∧ c g n - D1 ρ (fun x => ρ (r x) (e (s x))) g n = 0 := by
  have ha0 : ρ (r n) (e (s n)) = 0 := by rw [he0 _ (s_mem hrs hr hn), map_zero]
  constructor
  · simp only [D1]
    rw [hrn n hn, hsn n hn, ha0, h0 n hn, map_mul, Module.End.mul_apply]
    abel
  · simp only [D1]
    have hconj : g * n * g⁻¹ ∈ N := ‹N.Normal›.conj_mem n hn g
    have h1 : g * n = (g * n * g⁻¹) * g := by group
    have h2 : c g n = ρ (r g) (e (s g)) - ρ (g * n * g⁻¹) (ρ (r g) (e (s g))) := by
      have h3 : c g n = ρ (r g) (c (s g) n) := by
        conv_lhs => rw [← hrs g]
        exact mul_left_of_zero hc h0 _ (hr g) _ _
      have h4 := he (s g) (s g * n * (s g)⁻¹) (‹N.Normal›.conj_mem n hn _)
      have h5 : (s g)⁻¹ * (s g * n * (s g)⁻¹) * s g = n := by group
      rw [h5] at h4
      rw [h3, h4, map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      have key : ∀ a b : G, a * (b * n * b⁻¹) = (a * b) * n * (a * b)⁻¹ * a := by intros; group
      have key' := key (r g) (s g)
      rw [hrs] at key'
      rw [key']
    rw [ha0, map_zero, h1, hrn _ hconj, hsn _ hconj, h2, map_mul ρ (g * n * g⁻¹) (r g), Module.End.mul_apply]
    abel


include hc in
theorem stepC [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (h0' : ∀ n ∈ N, ∀ g, c g n = 0) (n : G) (hn : n ∈ N)
    (g h : G) : c g (h * n) = c g h ∧ c (g * n) h = c g h ∧ ρ n (c g h) = c g h := by
  have hR : ∀ g h n, n ∈ N → c g (h * n) = c g h := fun g h n hn => by
    have h1 := hc g h n
    simp only [h0' n hn, map_zero, zero_sub, sub_zero] at h1
    linear_combination (norm := abel) h1
  have hL : ∀ g h n, n ∈ N → c g (n * h) = c g h := fun g h n hn => by
    have : n * h = h * (h⁻¹ * n * h) := by group
    rw [this, hR _ _ _ (‹N.Normal›.conj_mem' n hn h)]
  have hM : ∀ g h n, n ∈ N → c (g * n) h = c g h := fun g h n hn => by
    have h1 := hc g n h
    simp only [h0 n hn, h0' n hn, map_zero, hL _ _ _ hn, zero_sub, sub_zero] at h1
    linear_combination (norm := abel) - h1
  refine ⟨hR g h n hn, hM g h n hn, ?_⟩
  rw [← mul_left_of_zero hc h0 n hn]
  have : n * g = g * (g⁻¹ * n * g) := by group
  rw [this, hM _ _ _ (‹N.Normal›.conj_mem' n hn g)]

end Alg

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Polynomial

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem finiteDimensional_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    FiniteDimensional ℚ_[p] (Kn p K n) := by
  have hnd := UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn
  have hm0 : 0 < qK p K ^ n - 1 := Nat.pos_of_ne_zero (by rintro h; exact hnd (h ▸ dvd_zero p))
  have hfin : Finite {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1} := by
    have : {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1} =
        (nthRootsFinset (qK p K ^ n - 1) (1 : PadicAlgCl p) : Set (PadicAlgCl p)) := by
      ext ζ
      simp [mem_nthRootsFinset hm0]
    rw [this]
    exact Finset.finite_toSet _
  have h2 : FiniteDimensional ℚ_[p]
      (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1}) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact IntermediateField.finiteDimensional_sup _ _

theorem extendScalars_Kn_eq_adjoin {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (qK p K ^ n - 1))
    (hm : qK p K ^ n - 1 ≠ 0) :
    IntermediateField.extendScalars (le_Kn p K n) = IntermediateField.adjoin K {ζ} := by
  apply le_antisymm
  · have h : Kn p K n ≤ (IntermediateField.adjoin K {ζ}).restrictScalars ℚ_[p] := by
      apply UnramifiedExtensions.Kn_le
      · intro y hy
        exact (IntermediateField.adjoin K {ζ}).algebraMap_mem ⟨y, hy⟩
      · intro ξ hξ
        have : NeZero (qK p K ^ n - 1) := ⟨hm⟩
        obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
        exact pow_mem (IntermediateField.mem_adjoin_simple_self K ζ) i
    exact h
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact mem_Kn_of_pow p K hζ.pow_eq_one

theorem natDegree_minpoly_le (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {ζ : PadicAlgCl p}
    (hζ : ζ ^ (qK p K ^ n - 1) = 1) : (minpoly K ζ).natDegree ≤ n := by
  classical
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hsep : (minpoly K ζ).Separable := (minpoly.irreducible hint).separable
  have hcard := card_rootSet_eq_natDegree (K := PadicAlgCl p) hsep (IsAlgClosed.splits _)
  calc (minpoly K ζ).natDegree = Fintype.card ((minpoly K ζ).rootSet (PadicAlgCl p)) := hcard.symm
    _ = ((minpoly K ζ).rootSet (PadicAlgCl p)).toFinset.card := (Set.toFinset_card _).symm
    _ ≤ ((Finset.range n).image (fun i => ζ ^ (qK p K ^ i))).card := by
        apply Finset.card_le_card
        intro y hy
        rw [Set.mem_toFinset] at hy
        obtain ⟨σ, hσ⟩ := ((isConjRoot_iff_mem_minpoly_rootSet hint).2 hy).symm.exists_algEquiv
        obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ
        exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, by rw [← h, hσ]⟩
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

theorem finrank_unramified_extension (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) = n ∧ qK p (Kn p K n) = qK p K ^ n := by
  have hq := one_lt_qK p K hK
  have hnd := UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn
  have hm0 : qK p K ^ n - 1 ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero p)
  obtain ⟨ζ, hζ⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hfd := finiteDimensional_Kn p K hK hn
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hup : Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) ≤ n := by
    rw [extendScalars_Kn_eq_adjoin p K hζ hm0, IntermediateField.adjoin.finrank hint]
    exact natDegree_minpoly_le p K hK hn hζ.pow_eq_one
  obtain ⟨f, hf, hqf, hle⟩ := qK_le_pow_finrank p K hK hfd (le_Kn p K n)
  have hmul := IntermediateField.finrank_bot_mul_relfinrank (le_Kn p K n)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_Kn p K n)] at hmul
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have h1 := UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ.pow_eq_one

  have hnf : n ≤ f := by
    have hmem : UnramifiedExtensions.red ζ ∈ resK p (Kn p K n) :=
      (UnramifiedExtensions.mem_resK_iff _ _).2 ⟨⟨ζ, mem_Obar_iff.2 h1.le⟩, mem_Kn_of_pow p K hζ.pow_eq_one,
        (UnramifiedExtensions.red_of_le h1.le).symm⟩
    have h2 := UnramifiedExtensions.pow_qK_eq (Kn p K n) hfd hmem
    rw [hqf, ← UnramifiedExtensions.red_pow h1.le] at h2
    have hζf : (ζ ^ (qK p K ^ f)) ^ (qK p K ^ n - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h3 : ζ ^ (qK p K ^ f) = ζ := by
      by_contra hne
      have h4 := UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one hnd hζf hζ.pow_eq_one hne
      have h5 := (UnramifiedExtensions.red_eq_iff (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζf).le h1.le).1 h2
      exact absurd h4 (ne_of_lt h5)
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [norm_zero] at h1; exact zero_ne_one h1
    have hf1 : 1 ≤ qK p K ^ f := Nat.one_le_pow _ _ (by omega)
    have h6 : ζ ^ (qK p K ^ f - 1) = 1 := by
      have h7 : qK p K ^ f = (qK p K ^ f - 1) + 1 := by omega
      rw [h7, pow_succ] at h3
      exact mul_right_cancel₀ hζ0 (by rw [h3, one_mul])
    have h8 := (hζ.pow_eq_one_iff_dvd _).1 h6
    have h9 : 1 < qK p K ^ f := Nat.one_lt_pow hf.ne' hq
    have h10 := Nat.le_of_dvd (by omega) h8
    have h11 : qK p K ^ n ≤ qK p K ^ f := by
      have : 1 ≤ qK p K ^ n := Nat.one_le_pow _ _ (by omega)
      omega
    exact (Nat.pow_le_pow_iff_right hq).1 h11
  have hkey : f * Module.finrank ℚ_[p] K ≤
      Module.finrank ℚ_[p] K * Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [hmul]; exact hle
  have hfle : f ≤ Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [mul_comm] at hkey
    exact Nat.le_of_mul_le_mul_left hkey hd
  have hfn : f = n := by omega
  exact ⟨by omega, by rw [hqf, hfn]⟩

theorem finrank_extendScalars_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) = n :=
  (finrank_unramified_extension p K hK hn).1

theorem finrank_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank ℚ_[p] (Kn p K n) = n * Module.finrank ℚ_[p] K := by
  have hmul := IntermediateField.finrank_bot_mul_relfinrank (le_Kn p K n)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_Kn p K n), finrank_extendScalars_Kn p K hK hn] at hmul
  rw [← hmul, mul_comm]

theorem qK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    qK p (Kn p K n) = qK p K ^ n :=
  (finrank_unramified_extension p K hK hn).2

theorem norm_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K n) : ∃ y ∈ K, ‖x‖ = ‖y‖ :=
  exists_norm_eq_of_qK p K hK (le_Kn p K n) hn (finrank_Kn p K hK hn) (qK_Kn p K hK hn) hx

theorem isGalois_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsGalois K (IntermediateField.extendScalars (le_Kn p K n)) := by
  have hnorm : Normal K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    rintro σ _ ⟨x, hx, rfl⟩
    exact map_mem_Kn p K n σ hx
  exact ⟨⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

