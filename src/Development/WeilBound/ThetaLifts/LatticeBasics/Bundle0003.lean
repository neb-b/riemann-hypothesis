module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.LocDistB
section
open Filter Topology GlobalTheory.WeilM

namespace GlobalTheory.ThK.Dbl.LD

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

noncomputable def ind (K : Subgroup G) : G → ℂ := Set.indicator (K : Set G) fun _ => 1

theorem ind_mem {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) : ind K ∈ SB G :=
  ⟨(LocallyConstant.charFn ℂ ⟨K.isClosed_of_isOpen ho, ho⟩).isLocallyConstant,
    HasCompactSupport.intro hc fun _ hx => Set.indicator_of_notMem hx _⟩

theorem ind_index (χ : G → ℂ) (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ)
    {H K : Subgroup G} (hHK : H ≤ K) (ho : IsOpen (H : Set G)) (hc : IsCompact (K : Set G)) (hχ : ∀ k ∈ K, χ k = 1) :
    l (ind K) = H.relIndex K * l (ind H) := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : DiscreteTopology (K ⧸ H.subgroupOf K) := QuotientGroup.discreteTopology (ho.preimage continuous_subtype_val)
  haveI : Fintype (K ⧸ H.subgroupOf K) := @Fintype.ofFinite _ finite_of_compact_of_discrete
  have hH := ind_mem ho (hc.of_isClosed_subset (H.isClosed_of_isOpen ho) hHK)
  have : ind K = ∑ q : K ⧸ H.subgroupOf K, fun x => ind H (x * q.out.1) := by
    ext x
    rw [Finset.sum_apply]
    by_cases hx : x ∈ K
    · have hmem : ∀ q : K ⧸ H.subgroupOf K, x * q.out.1 ∈ (H : Set G) ↔ ((⟨x, hx⟩⁻¹ : K) : K ⧸ H.subgroupOf K) = q := by
        intro q
        conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, inv_inv]
        rfl
      rw [Finset.sum_eq_single ((⟨x, hx⟩⁻¹ : K) : K ⧸ H.subgroupOf K)]
      · rw [ind, ind, Set.indicator_of_mem ((hmem _).2 rfl), Set.indicator_of_mem (by exact hx)]
      · intro q _ hq; exact Set.indicator_of_notMem (fun h => hq ((hmem q).1 h).symm) _
      · simp
    · rw [ind, Set.indicator_of_notMem (by exact hx)]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem
        (fun h => hx ((mul_mem_cancel_right q.out.2).1 (hHK h))) _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_sum, Finset.sum_congr rfl fun q _ => by rw [hl _ hH, hχ _ q.out.2, one_mul]]
  simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

theorem ind_zero (χ : G → ℂ) (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) (hχ : χ k ≠ 1) :
    l (ind K) = 0 := by
  have h := hl _ (ind_mem ho hc) k
  have : (fun x => ind K (x * k)) = ind K := by
    classical
    ext x; exact if_congr (K.mul_mem_cancel_right hk) rfl rfl
  rw [this] at h
  by_contra h0
  exact hχ (mul_right_cancel₀ h0 (by rw [← h, one_mul]))

theorem left_of_right (χ : G →* ℂ) (θ : G →* G) (cθ : Continuous θ) (iθ : ∀ x, θ (θ x) = x) {g : G} (hg : θ g = g⁻¹)
    (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ) {φ : G → ℂ} (hφ : φ ∈ SB G) :
    l (fun x => φ (g * x)) = χ g * l φ := by
  classical
  by_cases h0 : φ = 0
  · subst h0; exact (map_zero l).trans (by rw [map_zero, mul_zero])
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 h0
  let K₀ : Subgroup G :=
    { carrier := {k | ∀ x, φ (k * x) = φ x}
      one_mem' := fun x => by rw [one_mul]
      mul_mem' := fun {a b} ha hb x => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha x => by rw [← ha, mul_inv_cancel_left] }
  have o₀ : IsOpen (K₀ : Set G) := by
    refine K₀.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [sb_unif hφ (fun k x => k * x) (1 : G) (by fun_prop) one_mul,
      sb_unif hφ (fun k x => k⁻¹ * x) (1 : G) (by fun_prop) (by simp)] with k h1 h2 x
    by_cases hx : x ∈ tsupport φ
    · exact h1 x hx
    · by_cases hx' : k * x ∈ tsupport φ
      · simpa using (h2 _ hx').symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  have c₀ : IsCompact (K₀ : Set G) :=
    (IsCompact.image hφ.2 (continuous_mul_const x₀⁻¹)).of_isClosed_subset (K₀.isClosed_of_isOpen o₀) fun k hk =>
      ⟨k * x₀, subset_tsupport _ (by rw [Function.mem_support, hk x₀]; exact hx₀), by simp⟩
  let K := K₀ ⊓ K₀.comap θ
  have o : IsOpen (K : Set G) := o₀.inter (o₀.preimage cθ)
  have c : IsCompact (K : Set G) := c₀.of_isClosed_subset (K.isClosed_of_isOpen o) fun k hk => hk.1
  have hθ : ∀ x, θ x ∈ K ↔ x ∈ K := fun x => by
    show θ x ∈ K₀ ∧ θ (θ x) ∈ K₀ ↔ x ∈ K₀ ∧ θ x ∈ K₀
    rw [iθ]; exact and_comm
  let K' := K.comap (MulAut.conj g).toMonoidHom
  have hK' : ∀ x, x ∈ K' ↔ g * x * g⁻¹ ∈ K := fun x => Iff.rfl
  have hs : ind K' = fun x => ind K (g * x * g⁻¹) := rfl
  have o' : IsOpen (K' : Set G) := o.preimage (f := fun x => g * x * g⁻¹) (by fun_prop)
  have c' : IsCompact (K' : Set G) := (c.image (f := fun x => g⁻¹ * x * g) (by fun_prop)).of_isClosed_subset
    (K'.isClosed_of_isOpen o') fun x hx => ⟨_, (hK' x).1 hx, by group⟩
  have hconj : ∀ x, χ (g * x * g⁻¹) = χ x := fun x => by
    rw [map_mul, map_mul, mul_comm (χ g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have key : l (ind K') = l (ind K) := by
    by_cases hχ : ∀ k ∈ K, χ k = 1
    · have hχ' : ∀ k ∈ K', χ k = 1 := fun k hk => by rw [← hconj, hχ _ ((hK' k).1 hk)]
      rw [ind_index χ l hl (inf_le_left : K ⊓ K' ≤ K) (o.inter o') c hχ,
        ind_index χ l hl (inf_le_right : K ⊓ K' ≤ K') (o.inter o') c' hχ', Subgroup.inf_relIndex_left,
        Subgroup.inf_relIndex_right]
      let α := θ.comp (MulAut.conj g).toMonoidHom
      have hα : ∀ x, α x = θ (g * x * g⁻¹) := fun _ => rfl
      have e1 : K.comap α = K' := by ext x; rw [Subgroup.mem_comap, hα, hθ, hK']
      have e2 : K.map α = K' := by
        ext x
        rw [Subgroup.mem_map, hK']
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [hα, map_mul, map_mul, map_inv, hg]; simpa [mul_assoc] using (hθ y).2 hy
        · intro hx
          refine ⟨_, (hθ _).2 hx, ?_⟩
          rw [hα, map_mul, map_mul, map_inv, hg, iθ]; group
      conv_rhs => rw [← e1, Subgroup.relIndex_comap, e2, e1]
    · push Not at hχ
      obtain ⟨k, hk, hχ⟩ := hχ
      rw [ind_zero χ l hl o c hk hχ, ind_zero χ l hl o' c' (k := g⁻¹ * k * g) ((hK' _).2 (by simpa [mul_assoc] using hk))]
      rw [← hconj]; simpa [mul_assoc] using hχ
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology o
  have hfin : ((fun x : G => ((x⁻¹ : G) : G ⧸ K)) '' tsupport φ).Finite :=
    (IsCompact.image hφ.2 (QuotientGroup.continuous_mk.comp continuous_inv)).finite_of_discrete
  have hmem : ∀ (x : G) (q : G ⧸ K), x * q.out ∈ (K : Set G) ↔ ((x⁻¹ : G) : G ⧸ K) = q := by
    intro x q
    conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, inv_inv]
    rfl
  have dec : ∀ x, φ x = ∑ q ∈ hfin.toFinset, φ q.out⁻¹ * ind K (x * q.out) := fun x => by
    have hx : φ ((x⁻¹ : G) : G ⧸ K).out⁻¹ = φ x := by
      rw [← ((hmem x _).2 rfl).1, mul_inv_cancel_right]
    rw [Finset.sum_eq_single ((x⁻¹ : G) : G ⧸ K)]
    · rw [ind, Set.indicator_of_mem ((hmem x _).2 rfl), hx, mul_one]
    · intro q _ hq
      rw [ind, Set.indicator_of_notMem (fun h => hq ((hmem x q).1 h).symm), mul_zero]
    · intro h
      rw [hx, image_eq_zero_of_notMem_tsupport (f := φ) (x := x), zero_mul]
      exact fun hs => h (hfin.mem_toFinset.2 ⟨_, hs, rfl⟩)
  have d1 : φ = ∑ q ∈ hfin.toFinset, φ q.out⁻¹ • fun x => ind K (x * q.out) := by
    ext x; rw [dec x]; simp
  have d2 : (fun x => φ (g * x)) = ∑ q ∈ hfin.toFinset, φ q.out⁻¹ • fun x => ind K' (x * (q.out * g)) := by
    ext x; rw [dec, hs]; simp [mul_assoc]
  rw [d2]
  conv_rhs => rw [d1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, map_smul, hl _ (ind_mem o' c'), hl _ (ind_mem o c), key, map_mul, smul_eq_mul, smul_eq_mul]
  ring

end GlobalTheory.ThK.Dbl.LD
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.LocDistC
section
open Filter Topology GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.LD

variable {k : Type} [Field k] {n d : ℕ}

def blk (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) : Matrix (Fin (d + 1)) (Fin (d + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons a b) fun i => Fin.cons 0 (h i))

theorem det_blk (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) : (blk a b h).det = a * h.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have : (blk a b h).submatrix Fin.succ Fin.succ = h := by ext i j; simp [blk]
  simp [blk] at this ⊢
  simp [this]

theorem mul_blk_zero {m : Type} (X : Matrix m (Fin (d + 1)) k) (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) (i : m) :
    (X * blk a b h) i 0 = X i 0 * a := by simp [Matrix.mul_apply, Fin.sum_univ_succ, blk]

theorem mul_blk_succ {m : Type} (X : Matrix m (Fin (d + 1)) k) (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) (i : m)
    (j : Fin d) : (X * blk a b h) i j.succ = X i 0 * b j + ∑ s, X i s.succ * h s j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, blk]

theorem blk_comm (a : k) (b b' : Fin d → k) (hb : b = (a - 1) • b') :
    blk a 0 1 * blk 1 b' 1 = blk 1 b 1 * (blk 1 b' 1 * blk a 0 1) := by
  subst hb
  have hsum (f : Fin d → k) (j : Fin d) : ∑ x, f x * (1 : Matrix (Fin d) (Fin d) k) x j = f j := by
    simpa [Matrix.vecMul, dotProduct] using congrFun (Matrix.vecMul_one f) j
  ext i j
  rw [← Matrix.mul_assoc]
  refine Fin.cases ?_ (fun j => ?_) j <;> simp only [mul_blk_zero, mul_blk_succ] <;>
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [blk, hsum, one_apply]
  ring

def chE (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k :=
  ((fun i => X i 0, fun j => X 0 j.succ / X 0 0), Matrix.of fun i j => X i.succ j.succ - X i.succ 0 * (X 0 j.succ / X 0 0))

def chR (y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) : Matrix (Fin (n + 1)) (Fin (d + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons (y.1.1 0) fun j => y.1.1 0 * y.1.2 j)
    fun i => Fin.cons (y.1.1 i.succ) fun j => y.1.1 i.succ * y.1.2 j + y.2 i j)

theorem chR_chE (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (hX : X 0 0 ≠ 0) : chR (chE X) = X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [chR, chE]
  field_simp

theorem chE_chR (y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) (hy : y.1.1 0 ≠ 0) : chE (chR y) = y := by
  obtain ⟨⟨x, u⟩, W⟩ := y
  simp only at hy
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [chR, chE]
  · ext j; simp [chR, chE, hy]
  · ext i j; simp [chR, chE, hy]

theorem chE_unip (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (hX : X 0 0 ≠ 0) (b : Fin d → k) :
    chE (X * blk 1 b 1) = (((chE X).1.1, (chE X).1.2 + b), (chE X).2) := by
  have hsum (f : Fin d → k) (j : Fin d) : ∑ x, f x * (1 : Matrix (Fin d) (Fin d) k) x j = f j := by
    simpa [Matrix.vecMul, dotProduct] using congrFun (Matrix.vecMul_one f) j
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; simp [chE, mul_blk_zero]
  · ext j; simp [chE, mul_blk_zero, mul_blk_succ, hsum, one_apply]; field_simp; ring
  · ext i j; simp [chE, mul_blk_zero, mul_blk_succ, hsum, one_apply]; field_simp; ring

theorem chE_levi (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (h : Matrix (Fin d) (Fin d) k) :
    chE (X * blk 1 0 h) = (((chE X).1.1, (chE X).1.2 ᵥ* h), (chE X).2 * h) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; simp [chE, mul_blk_zero]
  · ext j
    simp only [chE, mul_blk_zero, mul_blk_succ, vecMul, dotProduct, Pi.zero_apply, mul_zero, zero_add, mul_one, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  · ext i j
    simp only [chE, mul_blk_zero, mul_blk_succ, of_apply, Pi.zero_apply, mul_zero, zero_add, mul_one, Finset.sum_div]
    rw [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by simp only [of_apply]; ring

def Deg {m : Type} (X : Matrix m (Fin d) k) : Prop := ∃ v ≠ 0, X *ᵥ v = 0

theorem Deg.chE {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k} (h : Deg X) (hX : X 0 0 ≠ 0) : Deg (chE X).2 := by
  obtain ⟨v, hv, h⟩ := h
  have hi : ∀ i, X i 0 * v 0 + ∑ j : Fin d, X i j.succ * v j.succ = 0 := fun i => by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ] using congrFun h i
  refine ⟨fun j => v j.succ, fun h0 => hv ?_, ?_⟩
  · have h1 : ∀ j : Fin d, v j.succ = 0 := congrFun h0
    ext j
    refine Fin.cases ?_ h1 j
    simpa [h1, hX] using hi 0
  · ext i
    have : ∑ j : Fin d, X i.succ 0 * (X 0 j.succ / X 0 0) * v j.succ = X i.succ 0 / X 0 0 * ∑ j : Fin d, X 0 j.succ * v j.succ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    simp only [LD.chE, mulVec, dotProduct, of_apply, sub_mul, Finset.sum_sub_distrib, this, Pi.zero_apply,
      eq_neg_of_add_eq_zero_right (hi 0), eq_neg_of_add_eq_zero_right (hi i.succ)]
    field_simp; ring

variable [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]

theorem sb_right {m : Type} {φ : Matrix m (Fin d) k → ℂ} (hφ : φ ∈ SB _) {h : Matrix (Fin d) (Fin d) k} (hh : h.det ≠ 0) :
    (fun y => φ (y * h)) ∈ SB (Matrix m (Fin d) k) :=
  sb_comp (· * h) (· * h⁻¹) (by fun_prop) (by fun_prop) (fun x => mul_nonsing_inv_cancel_right h x hh.isUnit) hφ

theorem cont_chE : ContinuousOn (chE (k := k) (n := n) (d := d)) {X | X 0 0 ≠ 0} := by
  have h : ∀ j : Fin d, ContinuousOn (fun X : Matrix (Fin (n + 1)) (Fin (d + 1)) k => X 0 j.succ / X 0 0) {X | X 0 0 ≠ 0} :=
    fun j => ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun _ h => h
  refine ContinuousOn.prodMk (ContinuousOn.prodMk (by fun_prop) (continuousOn_pi.2 h))
    (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_)
  exact ContinuousOn.sub (by fun_prop) (ContinuousOn.mul (by fun_prop) (h j))

theorem cont_chR : Continuous (chR (k := k) (n := n) (d := d)) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [chR] <;> fun_prop

theorem sb_chE {F : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k → ℂ} (hF : F ∈ SB _)
    (h0 : ∀ y, y.1.1 0 = 0 → F y = 0) : (fun X => F (chE X)) ∈ SB (Matrix (Fin (n + 1)) (Fin (d + 1)) k) :=
  sb_chart (U := {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k | X 0 0 ≠ 0})
    (T := {y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k | y.1.1 0 ≠ 0}) (isOpen_ne_fun (by fun_prop) continuous_const) cont_chE
    cont_chR.continuousOn chR_chE (fun y hy => by simpa [chR] using hy) hF (fun y hy => h0 y (not_not.1 hy))
    (fun _ _ => rfl) fun X hX => h0 _ (not_not.1 hX)

theorem sb_chR {φ : Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ} (hφ : φ ∈ SB _) (h0 : ∀ X, X 0 0 = 0 → φ X = 0) :
    (fun y => φ (chR y)) ∈ SB (((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) :=
  sb_chart (T := {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k | X 0 0 ≠ 0})
    (U := {y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k | y.1.1 0 ≠ 0}) (isOpen_ne_fun (by fun_prop) continuous_const)
    cont_chR.continuousOn cont_chE chE_chR (fun _ hy => hy) hφ (fun y hy => h0 y (not_not.1 hy))
    (fun _ _ => rfl) fun y hy => h0 _ (by simpa [chR] using hy)

def Eqv (c : k → ℂ) {m : Type} (l : (Matrix m (Fin d) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ h : Matrix (Fin d) (Fin d) k, h.det ≠ 0 → ∃ t : ℝ, 0 < t ∧ ∀ φ ∈ SB _, l (fun y => φ (y * h)) = c h.det * t * l φ

theorem Eqv.unip {c : k → ℂ} (hc : ∀ a ≠ 0, c a ≠ 0) {ϖ : k} (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) {m : Type}
    {l : (Matrix m (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} [Fintype m] (hl : Eqv c l) (b : Fin d → k) :
    ∀ φ ∈ SB _, l (fun y => φ (y * blk 1 b 1)) = l φ := by
  have hu : ∀ b : Fin d → k, (blk 1 b 1).det ≠ 0 := fun b => by simp [det_blk]
  have hD : (blk ϖ (0 : Fin d → k) 1).det ≠ 0 := by simp [det_blk, h0]
  obtain ⟨t₁, -, e₁⟩ := hl _ (hu b)
  obtain ⟨t₂, p₂, e₂⟩ := hl _ (hu ((ϖ - 1)⁻¹ • b))
  obtain ⟨t₃, p₃, e₃⟩ := hl _ hD
  intro φ hφ
  have a := e₃ _ (sb_right hφ (hu ((ϖ - 1)⁻¹ • b)))
  have a' := e₁ _ (sb_right (sb_right hφ hD) (hu ((ϖ - 1)⁻¹ • b)))
  simp only [Matrix.mul_assoc] at a a'
  rw [blk_comm ϖ b _ (by rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.2 h1), one_smul]), a', e₂ _ hφ] at a
  have a2 := e₂ _ (sb_right hφ hD)
  simp only [Matrix.mul_assoc] at a2
  rw [a2, e₃ _ hφ] at a
  rw [e₁ _ hφ]
  have n2 : c (blk 1 ((ϖ - 1)⁻¹ • b) 1).det * t₂ ≠ 0 := mul_ne_zero (hc _ (hu _)) (by exact_mod_cast p₂.ne')
  have n3 : c (blk ϖ (0 : Fin d → k) 1).det * t₃ ≠ 0 := mul_ne_zero (hc _ hD) (by exact_mod_cast p₃.ne')
  apply mul_left_cancel₀ (mul_ne_zero n2 n3)
  linear_combination a

end GlobalTheory.ThK.Dbl.LD
end

