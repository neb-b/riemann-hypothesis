module

public import Mathlib
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistenceOfSandwichStatement
section
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.RgFl.MaxLat

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]

theorem herm_add_left {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (x y z : V) :
    h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add (f := _), ← hh.2.2.1 z x, ← hh.2.2.1 z y]

def hLin {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (z : V) : V →ₗ[L] L where
  toFun := h z
  map_add' := hh.1 z
  map_smul' a y := by simpa using hh.2.1 a z y

theorem herm_eq_sum {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) {ι : Type} [Fintype ι]
    (b : Module.Basis ι L V) (z y : V) : h z y = ∑ j, b.repr y j * h z (b j) := by
  calc h z y = hLin hh z y := rfl
    _ = hLin hh z (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.repr y j * h z (b j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      rfl

theorem norm_sub_le_max_of_ultrametric_field (a b : L) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)

theorem norm_herm_le_delta {s : L →+* L} {δ : L} {h : V → V → L} (hδ : IsDelta s δ)
    (hh : IsHerm s h) {M : AddSubgroup V} (hO : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hM : ∀ x ∈ M, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ M) (hy : y ∈ M) : ‖h x y‖ ≤ ‖δ‖ := by
  refine (hδ.2.1 (h x y)).1 fun t ht => ?_
  have hy' : t • y ∈ M := hO t ht y hy
  have e1 : h x (t • y) = h x y * t := by rw [hh.2.1, mul_comm]
  have e2 : h (t • y) x = s (h x y * t) := by rw [hh.2.2.1 x (t • y), e1]
  have e3 : h (x + t • y) (x + t • y)
      = h x x + (h x y * t + s (h x y * t)) + h (t • y) (t • y) := by
    rw [herm_add_left hh, hh.1, hh.1, e1, e2]; ring
  have e4 : h x y * t + s (h x y * t)
      = h (x + t • y) (x + t • y) - h x x - h (t • y) (t • y) := by
    rw [e3]; ring
  rw [e4]
  exact (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le
    ((norm_sub_le_max_of_ultrametric_field _ _).trans
      (max_le (hM _ (M.add_mem hx hy')) (hM _ hx))) (hM _ hy'))

theorem exists_basis_herm_le_one [FiniteDimensional L V] {s : L →+* L} {h : V → V → L}
    (hs : IsInv s) (hh : IsHerm s h) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) L V), ∀ i j, ‖h (b i) (b j)‖ ≤ 1 := by
  let e := Module.finBasis L V
  let K : ℝ := ∑ i, ∑ j, ‖h (e i) (e j)‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hKij : ∀ i j, ‖h (e i) (e j)‖ ≤ K := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖h (e i) (e j)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖h (e i) (e j)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  obtain ⟨t, ht0, ht⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (K + 1) by positivity)
  have htK : ‖t‖ * (K + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at ht
    exact ht.le
  have ht1 : ‖t‖ ≤ 1 := by nlinarith [norm_nonneg t]
  have htK' : ‖t‖ * K ≤ 1 := by nlinarith [norm_nonneg t]
  have tne : t ≠ 0 := norm_pos_iff.1 ht0
  have hu : ∀ i : Fin (Module.finrank L V), IsUnit ((fun _ => t) i : L) :=
    fun _ => isUnit_iff_ne_zero.2 tne
  refine ⟨_, e.isUnitSMul hu, fun i j => ?_⟩
  simp only [Module.Basis.isUnitSMul_apply]
  have e1 : h (t • e i) (t • e j) = t * (s t * h (e i) (e j)) := by
    rw [hh.2.1, hh.2.2.1 (e j) (t • e i), hh.2.1, map_mul, ← hh.2.2.1 (e j) (e i)]
  rw [e1, norm_mul, norm_mul, hs.2.1]
  calc ‖t‖ * (‖t‖ * ‖h (e i) (e j)‖) ≤ 1 * (‖t‖ * K) := by
        gcongr
        exact hKij i j
    _ ≤ 1 := by linarith

def ball {ι : Type} (b : Module.Basis ι L V) : AddSubgroup V where
  carrier := {x | ∀ i, ‖b.repr x i‖ ≤ 1}
  add_mem' {x y} hx hy i := by
    simpa using (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) (hy i))
  zero_mem' i := by simp
  neg_mem' {x} hx i := by simpa using hx i

theorem basis_mem_ball {ι : Type} [DecidableEq ι] (b : Module.Basis ι L V) (j : ι) :
    b j ∈ ball b := by
  intro i
  rw [b.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem IsLat.smul_mem {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V}
    (hx : x ∈ Λ) : a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  simpa using mul_le_one₀ ha (norm_nonneg _) (hx i)

theorem ball_absorbing {m : ℕ} (b : Module.Basis (Fin m) L V) (x : V) :
    ∃ a : L, a ≠ 0 ∧ a • x ∈ ball b := by
  let K : ℝ := ∑ i, ‖b.repr x i‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨t, ht0, ht⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (K + 1) by positivity)
  have htK : ‖t‖ * (K + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at ht
    exact ht.le
  refine ⟨t, norm_pos_iff.1 ht0, fun i => ?_⟩
  have hi : ‖b.repr x i‖ ≤ K :=
    Finset.single_le_sum (f := fun i => ‖b.repr x i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  nlinarith [norm_nonneg t, norm_nonneg (b.repr x i)]

theorem norm_herm_ball_le_one {s : L →+* L} {h : V → V → L} (hs : IsInv s) (hh : IsHerm s h)
    {m : ℕ} (b : Module.Basis (Fin m) L V) (hb : ∀ i j, ‖h (b i) (b j)‖ ≤ 1) {x : V}
    (hx : x ∈ ball b) : ‖h x x‖ ≤ 1 := by
  have h1 : ∀ j, ‖h (b j) x‖ ≤ 1 := fun j => by
    rw [herm_eq_sum hh b]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hx i) (norm_nonneg _) (hb j i)
  rw [herm_eq_sum hh b]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  rw [norm_mul, hh.2.2.1 (b j) x, hs.2.1]
  exact mul_le_one₀ (hx j) (norm_nonneg _) (h1 j)

theorem exists_scale {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (B : ℝ) (hB : 0 ≤ B)
    {m : ℕ} (b : Module.Basis (Fin m) L V) :
    ∃ c : L, c ≠ 0 ∧ ∀ x, (∀ j, ‖h (b j) x‖ ≤ B) → c • x ∈ ball b := by
  let T : V →ₗ[L] (Fin m → L) := LinearMap.pi fun j => hLin hh (b j)
  have hT : LinearMap.ker T = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => hh.2.2.2 x fun y => ?_
    have hj : ∀ j, h (b j) x = 0 := fun j => congrFun hx j
    rw [herm_eq_sum hh b]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hh.2.2.1 (b j) x, hj j, map_zero, mul_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hT
  let w : Fin m → V := fun k => g fun j => if k = j then 1 else 0
  have hx : ∀ x, x = ∑ k, h (b k) x • w k := fun x => by
    have h1 : g (T x) = x := by simpa using LinearMap.congr_fun hg x
    have h2 := LinearMap.pi_apply_eq_sum_univ g (T x)
    rw [h1] at h2
    exact h2
  let C : ℝ := ∑ k, ∑ i, ‖b.repr (w k) i‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hCki : ∀ k i, ‖b.repr (w k) i‖ ≤ C := fun k i =>
    (Finset.single_le_sum (f := fun i => ‖b.repr (w k) i‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun k => ∑ i, ‖b.repr (w k) i‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  obtain ⟨c, hc0, hc⟩ :=
    NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (B * C + 1) by positivity)
  have hcK : ‖c‖ * (B * C + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hc
    exact hc.le
  refine ⟨c, norm_pos_iff.1 hc0, fun x hxB i => ?_⟩
  have hr : b.repr x i = ∑ k, h (b k) x * b.repr (w k) i := by
    conv_lhs => rw [hx x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finsupp.finsetSum_apply]
  have hbound : ‖b.repr x i‖ ≤ B * C := by
    rw [hr]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hxB k) (hCki k i) (norm_nonneg _) hB
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  nlinarith [norm_nonneg c, norm_nonneg (b.repr x i)]

theorem stExists_of_stSandwich : StSandwich → StExists := by
  intro hSw
  unfold StExists ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh
  obtain ⟨m, b, hb⟩ := exists_basis_herm_le_one hs hh
  obtain ⟨c, hc0, hc⟩ := exists_scale hh ‖δ‖ (norm_nonneg _) b
  let S : Set (AddSubgroup V) :=
    {Λ | (∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ Λ, a • x ∈ Λ) ∧ ∀ x ∈ Λ, ‖h x x‖ ≤ 1}
  have hlat0 : IsLat L (ball b) := ⟨m, b, fun _ => Iff.rfl⟩
  have hS0 : ball b ∈ S :=
    ⟨fun a ha x hx => IsLat.smul_mem hlat0 ha hx, fun x hx => norm_herm_ball_le_one hs hh b hb hx⟩
  have hchain : ∀ C ⊆ S, IsChain (· ≤ ·) C → ∀ y ∈ C, ∃ ub ∈ S, ∀ z ∈ C, z ≤ ub := by
    intro C hCS hC y hy
    have hmem : ∀ x, x ∈ sSup C ↔ ∃ t ∈ C, x ∈ t := fun x =>
      AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hC.directedOn
    refine ⟨sSup C, ⟨fun a ha x hx => ?_, fun x hx => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨t, ht, hxt⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨t, ht, (hCS ht).1 a ha x hxt⟩
    · obtain ⟨t, ht, hxt⟩ := (hmem x).1 hx
      exact (hCS ht).2 x hxt
  obtain ⟨M, hM0, hMax⟩ := zorn_le_nonempty₀ S hchain (ball b) hS0
  have hMlat : IsLat L M := by
    refine hSw L V (ball b) M c hlat0 hc0 (fun x hx => hc x fun j => ?_) (fun x => ?_) hMax.prop.1
    · exact norm_herm_le_delta hδ hh hMax.prop.1 hMax.prop.2 (hM0 (basis_mem_ball b j)) hx
    · obtain ⟨a, ha, hax⟩ := ball_absorbing b x
      exact ⟨a, ha, hM0 hax⟩
  refine ⟨M, hMlat, hMax.prop.2, fun Λ' hL hI hle => ?_⟩
  exact le_antisymm (hMax.2 ⟨fun a ha x hx => IsLat.smul_mem hL ha hx, hI⟩ hle) hle

end GlobalTheory.CompanionTheory.RgFl.MaxLat

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FrameOfAnisotropicPlaneSplitting
section
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermFrame

section Steps

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem herm_smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  obtain ⟨_, h2, h3, _⟩ := hh
  rw [h3 y (a • x), h2, map_mul, ← h3 y x]

theorem herm_symm_zero (hh : IsHerm s h) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  rw [hh.2.2.1 x y, hxy, map_zero]

theorem herm_right_zero (hh : IsHerm s h) (x : V) : h x 0 = 0 := by
  have := hh.2.1 (0 : L) x 0
  simpa using this

def orthPair (hh : IsHerm s h) (e f : V) : Submodule L V where
  carrier := {x | h e x = 0 ∧ h f x = 0}
  add_mem' := by
    intro a b ha hb
    exact ⟨by rw [hh.1, ha.1, hb.1, add_zero], by rw [hh.1, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨herm_right_zero hh e, herm_right_zero hh f⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by rw [hh.2.1, hx.1, mul_zero], by rw [hh.2.1, hx.2, mul_zero]⟩

theorem frame_cons (hh : IsHerm s h) {δ : L} {e f : V} {U : Submodule L V}
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) (hee : h e e = 0) (hff : h f f = 0) (hef : h e f = δ)
    (hdec : ∀ x, ∃ (a b : L), ∃ w ∈ U, x = a • e + b • f + w) {l : ℕ} {e' f' : Fin l → U}
    {W' : Submodule L U} (hfr : IsFrame (fun x y : U => h x y) δ e' f' W') :
    IsFrame h δ (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hfr
  have heU : ∀ x ∈ U, h e x = 0 := fun x hx => ((hU x).1 hx).1
  have hfU : ∀ x ∈ U, h f x = 0 := fun x hx => ((hU x).1 hx).2
  have heU' : ∀ x ∈ U, h x e = 0 := fun x hx => herm_symm_zero hh (heU x hx)
  have hfU' : ∀ x ∈ U, h x f = 0 := fun x hx => herm_symm_zero hh (hfU x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hee
      | succ j => simpa using heU _ (e' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using heU' _ (e' i).2
      | succ j => simpa using a1 i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hff
      | succ j => simpa using hfU _ (f' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using hfU' _ (f' i).2
      | succ j => simpa using a2 i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hef
      | succ j =>
        simpa [Ne.symm (Fin.succ_ne_zero j)] using heU _ (f' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa [Fin.succ_ne_zero i] using hfU' _ (e' i).2
      | succ j => simpa using a3 i j
  · intro w hw i
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
    induction i using Fin.cases with
    | zero => simpa using And.intro (heU _ w'.2) (hfU _ w'.2)
    | succ i => simpa using a4 w' hw' i
  · intro w hw h0
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
    have : w' = 0 := a5 w' hw' h0
    simp [this]
  · intro x
    obtain ⟨a, b, w, hw, rfl⟩ := hdec x
    obtain ⟨a', b', w', hw', hEq⟩ := a6 ⟨w, hw⟩
    refine ⟨Fin.cons a a', Fin.cons b b', U.subtype w', Submodule.mem_map_of_mem hw', ?_⟩
    have hw2 : w = ∑ i, a' i • (e' i : V) + ∑ i, b' i • (f' i : V) + (w' : V) := by
      have := congrArg Subtype.val hEq
      simpa using this
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
    rw [hw2]
    abel

theorem adapted_cons {U : Submodule L V} {e f : V} {l : ℕ} {e' f' : Fin l → U} {W' : Submodule L U}
    {u0 : L} {u' : Fin l → L} {Λ : AddSubgroup V}
    (hsp : ∀ (a b : L), ∀ w ∈ U, (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ ‖u0‖ ∧ ‖b‖ ≤ ‖u0‖⁻¹ ∧ w ∈ Λ))
    (had : IsAdapted (fun x y : U => h x y) e' f' W' u' (Λ.comap U.subtype.toAddMonoidHom)) :
    IsAdapted h (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype)
      (Fin.cons u0 u' : Fin (l + 1) → L) Λ := by
  intro a b w hw
  obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
  have hc := had (fun i => a i.succ) (fun i => b i.succ) w' hw'
  obtain ⟨w0, hw0⟩ : ∃ w0 : U, w0 = ∑ i, a i.succ • e' i + ∑ i, b i.succ • f' i + w' := ⟨_, rfl⟩
  rw [← hw0] at hc
  have hval : (w0 : V) = ∑ i, a i.succ • (e' i : V) + ∑ i, b i.succ • (f' i : V) + (w' : V) := by
    rw [hw0]
    simp
  have hrw : ∑ i, a i • (Fin.cons e (fun i => (e' i : V)) : Fin (l + 1) → V) i +
      ∑ i, b i • (Fin.cons f (fun i => (f' i : V)) : Fin (l + 1) → V) i + U.subtype w' =
      a 0 • e + b 0 • f + (w0 : V) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hval]
    simp only [Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
    abel
  have hc' : (w0 : V) ∈ Λ ↔ (∀ i, ‖a i.succ‖ ≤ ‖u' i‖) ∧ (∀ i, ‖b i.succ‖ ≤ ‖u' i‖⁻¹) ∧
      ‖h w' w'‖ ≤ 1 := hc
  rw [hrw, hsp _ _ _ w0.2, hc']
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
  tauto

end Steps

theorem exists_adapted_frame_with_unit_scaling (hA : StAniso) (hP : StPlane) (hS : StSplit)
    (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L]
    (s : L →+* L) (hs : IsInv s) (δ : L) (hδ : IsDelta s δ) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (h : V → V → L),
      Module.finrank L V = n → IsHerm s h → ∀ Λ Λ' : AddSubgroup V, IsMax h Λ → IsMax h Λ' →
      ∃ (l : ℕ) (e f : Fin l → V) (W : Submodule L V) (u : Fin l → L), (∀ i, u i ≠ 0) ∧
        IsFrame h δ e f W ∧ IsAdapted h e f W (fun _ => 1) Λ ∧ IsAdapted h e f W u Λ' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ h hn hh Λ Λ' hΛ hΛ'
  by_cases hiso : ∃ x, x ≠ 0 ∧ h x x = 0
  · obtain ⟨e, f, u, hu, hee, hff, hef, he, hf, hue, hvf⟩ :=
      hP L s hs δ hδ V h hh hiso Λ Λ' hΛ hΛ'
    have hUm : ∀ x, x ∈ orthPair hh e f ↔ h e x = 0 ∧ h f x = 0 := fun x => Iff.rfl
    obtain ⟨hUh, hdec, hUtop, hmax⟩ := hS L s hs δ hδ V h hh e f (orthPair hh e f) hee hff hef hUm
    have hsu : s u ≠ 0 := (map_ne_zero s).2 hu
    have hee' : h (u • e) (u • e) = 0 := by
      rw [herm_smul_left hh, hh.2.1, hee, mul_zero, mul_zero]
    have hff' : h ((s u)⁻¹ • f) ((s u)⁻¹ • f) = 0 := by
      rw [herm_smul_left hh, hh.2.1, hff, mul_zero, mul_zero]
    have hef' : h (u • e) ((s u)⁻¹ • f) = δ := by
      rw [herm_smul_left hh, hh.2.1, hef, ← mul_assoc, mul_inv_cancel₀ hsu, one_mul]
    have hUm' : ∀ x, x ∈ orthPair hh e f ↔ h (u • e) x = 0 ∧ h ((s u)⁻¹ • f) x = 0 := by
      intro x
      rw [hUm, herm_smul_left hh, herm_smul_left hh]
      have hsi' : s ((s u)⁻¹) ≠ 0 := (map_ne_zero s).2 (inv_ne_zero hsu)
      simp [hsu, hsi']
    obtain ⟨-, -, -, hmax'⟩ :=
      hS L s hs δ hδ V h hh (u • e) ((s u)⁻¹ • f) (orthPair hh e f) hee' hff' hef' hUm'
    obtain ⟨m1, p1⟩ := hmax Λ hΛ he hf
    obtain ⟨m2, p2⟩ := hmax' Λ' hΛ' hue hvf
    have hlt : Module.finrank L (orthPair hh e f) < n := hn ▸ Submodule.finrank_lt hUtop
    obtain ⟨l, e', f', W', u', hu', hfr, ad1, ad2⟩ :=
      ih _ hlt (orthPair hh e f) (fun x y => h x y) rfl hUh _ _ m1 m2
    have hsp1 : ∀ (a b : L), ∀ w ∈ orthPair hh e f,
        (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ ‖(1 : L)‖ ∧ ‖b‖ ≤ ‖(1 : L)‖⁻¹ ∧ w ∈ Λ) := by
      intro a b w hw
      simp only [norm_one, inv_one]
      exact p1 a b w hw
    have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hsp2 : ∀ (a b : L), ∀ w ∈ orthPair hh e f,
        (a • e + b • f + w ∈ Λ' ↔ ‖a‖ ≤ ‖u‖ ∧ ‖b‖ ≤ ‖u‖⁻¹ ∧ w ∈ Λ') := by
      intro a b w hw
      have key := p2 (a * u⁻¹) (b * s u) w hw
      have e1 : (a * u⁻¹) • (u • e) + (b * s u) • ((s u)⁻¹ • f) + w = a • e + b • f + w := by
        rw [smul_smul, smul_smul, mul_assoc, mul_assoc, inv_mul_cancel₀ hu,
          mul_inv_cancel₀ hsu, mul_one, mul_one]
      rw [e1] at key
      rw [key, norm_mul, norm_mul, norm_inv, hs.2.1 u, ← div_eq_mul_inv, div_le_one hpos,
        ← one_div, le_div_iff₀ hpos]
    have h1 : (fun _ : Fin (l + 1) => (1 : L)) = Fin.cons 1 (fun _ : Fin l => (1 : L)) := by
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => rfl
    refine ⟨l + 1, Fin.cons e fun i => (e' i : V), Fin.cons f fun i => (f' i : V),
      W'.map (orthPair hh e f).subtype, Fin.cons u u', ?_,
      frame_cons hh hUm hee hff hef hdec hfr, ?_, adapted_cons hsp2 ad2⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hu
      | succ i => simpa using hu' i
    · rw [h1]
      exact adapted_cons hsp1 ad1
  · have hiso' : ∀ x, h x x = 0 → x = 0 := by
      intro x hx
      by_contra hne
      exact hiso ⟨x, hne, hx⟩
    have hm : ∀ M : AddSubgroup V, IsMax h M → ∀ x, x ∈ M ↔ ‖h x x‖ ≤ 1 :=
      fun M hM => hA L s hs δ hδ V h hh hiso' M hM
    refine ⟨0, Fin.elim0, Fin.elim0, ⊤, Fin.elim0, fun i => i.elim0,
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ _ i => i.elim0,
        fun w _ hw => hiso' w hw, fun x => ⟨Fin.elim0, Fin.elim0, x, trivial, by simp⟩⟩, ?_, ?_⟩
    · intro a b w _
      simp [hm Λ hΛ]
    · intro a b w _
      simp [hm Λ' hΛ']

theorem stFrame_of : StAniso → StPlane → StSplit → StFrame := by
  intro hA hP hS L _ _ _ _ s hs δ hδ V _ _ _ h hh
  exact exists_adapted_frame_with_unit_scaling hA hP hS L s hs δ hδ _ V h rfl hh

end GlobalTheory.CompanionTheory.HermFrame

end
end

