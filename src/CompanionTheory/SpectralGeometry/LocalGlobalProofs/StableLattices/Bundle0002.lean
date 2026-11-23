module

public import Mathlib
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AnisotropicOfHenselAndSandwich
section
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermAniso

section Core

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

lemma add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  have h1 := hh.2.2.1
  rw [h1 z (x + y), hh.1, map_add (f := _), h1 z x, h1 z y]

lemma smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  have h1 := hh.2.2.1
  rw [h1 y (a • x), hh.2.1, map_mul, h1 y x]

lemma q_add (hh : IsHerm s h) (x y : V) :
    h (x + y) (x + y) = h x x + h y y + (h x y + h y x) := by
  rw [add_left hh, hh.1, hh.1]; ring

lemma norm_q_smul (hs : IsInv s) (hh : IsHerm s h) (a : L) (x : V) :
    ‖h (a • x) (a • x)‖ = ‖a‖ * ‖a‖ * ‖h x x‖ := by
  rw [smul_left hh, hh.2.1, norm_mul, norm_mul, hs.2.1]; ring

lemma pair_le [IsUltrametricDist L] [CompleteSpace L] (hH : StHensel) (hs : IsInv s) (hh : IsHerm s h)
    (hani : ∀ x, h x x = 0 → x = 0) {x y : V} (hx : ‖h x x‖ ≤ 1) (hy : ‖h y y‖ ≤ 1) :
    ‖h x y + h y x‖ ≤ 1 := by
  have h1 := hh.2.2.1
  by_contra hb
  push_neg at hb
  obtain ⟨b, hbd⟩ : ∃ b, b = h x y + h y x := ⟨_, rfl⟩
  rw [← hbd] at hb
  have hbpos : 0 < ‖b‖ := by linarith
  have hb0 : b ≠ 0 := norm_pos_iff.mp hbpos
  have hsb : s b = b := by
    rw [hbd, map_add (f := _), ← h1 x y, ← h1 y x, add_comm]
  have hsx : s (h x x) = h x x := (h1 x x).symm
  have hsy : s (h y y) = h y y := (h1 y y).symm
  have hc1 : s (h y y / b ^ 2) = h y y / b ^ 2 := by
    rw [map_div₀, map_pow, hsb, hsy]
  have hc2 : ‖h y y / b ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨u, hsu, hu, he⟩ := hH L s hs (h y y / b ^ 2) (h x x) hc1 hsx hc2 hx
  obtain ⟨t, htd⟩ : ∃ t, t = u / b := ⟨_, rfl⟩
  have hst : s t = t := by rw [htd, map_div₀, hsu, hsb]
  have hq : h (x + t • y) (x + t • y) = 0 := by
    rw [q_add hh, smul_left hh, hh.2.1, hh.2.1, smul_left hh, hst]
    have e1 : t * (t * h y y) + t * h x y + t * h y x = t * b + t ^ 2 * h y y := by
      rw [hbd]; ring
    have e2 : t * b = u := by rw [htd]; field_simp
    have e3 : t ^ 2 * h y y = h y y / b ^ 2 * u ^ 2 := by rw [htd]; field_simp
    linear_combination he + e1 + e2 + e3
  have hz := hani _ hq
  have hxe : x = (-t) • y := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hz
  have hxy : h x y = -t * h y y := by
    have : h x y = h ((-t) • y) y := congrArg (fun z => h z y) hxe
    rw [this, smul_left hh, map_neg, hst]
  have hyx : h y x = -t * h y y := by
    have : h y x = h y ((-t) • y) := congrArg (fun z => h y z) hxe
    rw [this, hh.2.1]
  have ht : ‖t‖ < 1 := by
    rw [htd, norm_div, div_lt_one hbpos]; linarith
  have hle : ‖-t * h y y‖ < 1 := by
    rw [norm_mul, norm_neg]
    nlinarith [norm_nonneg t, norm_nonneg (h y y)]
  have : ‖b‖ < 1 := by
    rw [hbd, hxy, hyx]
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (by simp)) hle
  linarith

lemma exists_ball [IsUltrametricDist L] (hs : IsInv s) (hh : IsHerm s h)
    (hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1) :
    ∃ V₀ : AddSubgroup V, ∀ x, x ∈ V₀ ↔ ‖h x x‖ ≤ 1 := by
  refine ⟨{ carrier := {x | ‖h x x‖ ≤ 1}, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun x => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [q_add hh]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp a b ha hb))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  · have := hh.2.1 (0 : L) (0 : V) (0 : V)
    simp only [zero_smul, zero_mul] at this
    simp [this]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := norm_q_smul hs hh (-1 : L) a
    simp only [neg_smul, one_smul, norm_neg, norm_one, one_mul] at this
    rwa [this]

lemma coord_comb [FiniteDimensional L V] (hh : IsHerm s h) {m : ℕ} (b : Module.Basis (Fin m) L V) :
    ∃ M : Fin m → Fin m → L, ∀ x i, b.repr x i = ∑ j, M i j * h (b j) x := by
  have h1 := hh.2.2.1
  let φ : V →ₗ[L] (Fin m → L) :=
    { toFun := fun x j => h (b j) x
      map_add' := fun x y => by ext j; simp [hh.1]
      map_smul' := fun a x => by ext j; simp [hh.2.1] }
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    let ℓ : V →ₗ[L] L :=
      { toFun := fun y => h x y
        map_add' := fun y z => hh.1 x y z
        map_smul' := fun a y => by simp [hh.2.1] }
    have hl : ℓ = 0 := by
      refine b.ext fun j => ?_
      have : h (b j) x = 0 := congrFun hx j
      change h x (b j) = 0
      rw [h1 (b j) x, this, map_zero]
    exact hh.2.2.2 x fun y => LinearMap.congr_fun hl y
  obtain ⟨ψ, hψ⟩ := φ.exists_leftInverse_of_injective hker
  refine ⟨fun i j => ((b.coord i) ∘ₗ ψ) (fun k => if j = k then 1 else 0), fun x i => ?_⟩
  have e : ψ (φ x) = x := LinearMap.congr_fun hψ x
  have := LinearMap.pi_apply_eq_sum_univ ((b.coord i) ∘ₗ ψ) (φ x)
  simp only [LinearMap.comp_apply, Module.Basis.coord_apply, smul_eq_mul, e] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  rfl

end Core

theorem aniso : StHensel → StSandwich → StAniso := by
  intro hH hS
  unfold StAniso ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh hani Λ hΛ x
  have h1 := hh.2.2.1
  have hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1 :=
    fun x y hx hy => pair_le hH hs hh hani hx hy
  obtain ⟨V₀, hV₀⟩ := exists_ball hs hh hp
  have hsmul : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ V₀, a • x ∈ V₀ := by
    intro a ha x hx
    rw [hV₀] at hx ⊢
    rw [norm_q_smul hs hh]
    have := norm_nonneg a
    have h2 := norm_nonneg (h x x)
    calc ‖a‖ * ‖a‖ * ‖h x x‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hδle : ∀ x ∈ V₀, ∀ y ∈ V₀, ‖h x y‖ ≤ ‖δ‖ := by
    intro x hx y hy
    refine (hδ.2.1 (h x y)).mp fun a ha => ?_
    have hay := hsmul a ha y hy
    have := hp x (a • y) ((hV₀ x).mp hx) ((hV₀ _).mp hay)
    rw [h1 x (a • y), hh.2.1] at this
    rwa [mul_comm]
  have hle : Λ ≤ V₀ := fun y hy => (hV₀ y).mpr (hΛ.2.1 y hy)
  obtain ⟨m, b, hb⟩ := hΛ.1
  have hbΛ : ∀ j, b j ∈ Λ := by
    intro j
    rw [hb]
    intro i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  obtain ⟨M, hM⟩ := coord_comb hh b
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ V₀, ∀ i, ‖b.repr x i‖ ≤ C := by
    refine ⟨∑ i, ∑ j, ‖M i j‖ * ‖δ‖ + 1, ?_, fun x hx i => ?_⟩
    · have : 0 ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖ :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
      linarith
    · have e1 : ‖b.repr x i‖ ≤ ∑ j, ‖M i j‖ * ‖δ‖ := by
        rw [hM]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hδle _ (hle (hbΛ j)) x hx) (norm_nonneg _)
      have e2 : ∑ j, ‖M i j‖ * ‖δ‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ * ‖δ‖)
          (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i)
      linarith
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt L (inv_pos.mpr hC0)
  have hcne : c ≠ 0 := norm_pos_iff.mp hc0
  have hbound : ∀ x ∈ V₀, c • x ∈ Λ := by
    intro x hx
    rw [hb]
    intro i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
    have e := hC x hx i
    have e2 : ‖c‖ * C ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hc1.le hC0.le
      rwa [inv_mul_cancel₀ hC0.ne'] at this
    calc ‖c‖ * ‖b.repr x i‖ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left e hc0.le
      _ ≤ 1 := e2
  have hab : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ V₀ := by
    intro x
    have hpos : (0 : ℝ) < (1 + ‖h x x‖)⁻¹ := by positivity
    obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt L hpos
    refine ⟨a, norm_pos_iff.mp ha0, ?_⟩
    rw [hV₀, norm_q_smul hs hh]
    have hq := norm_nonneg (h x x)
    have e1 : ‖a‖ * (1 + ‖h x x‖) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ha1.le (by positivity : (0 : ℝ) ≤ 1 + ‖h x x‖)
      rwa [inv_mul_cancel₀ (by positivity)] at this
    have e2 : ‖a‖ ≤ 1 := by nlinarith
    have e3 : ‖a‖ * ‖h x x‖ ≤ 1 := by nlinarith
    calc ‖a‖ * ‖a‖ * ‖h x x‖ = ‖a‖ * (‖a‖ * ‖h x x‖) := by ring
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hlat : IsLat L V₀ :=
    hS L V Λ V₀ c ⟨m, b, hb⟩ hcne hbound hab hsmul
  have heq : V₀ = Λ := hΛ.2.2 V₀ hlat (fun x hx => (hV₀ x).mp hx) hle
  rw [← heq]
  exact hV₀ x

end GlobalTheory.CompanionTheory.HermAniso

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DeltaStatement
section
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.RgFl

theorem exists_isDelta (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    [CharZero L] (s : L →+* L) (hs : IsInv s) : ∃ δ, IsDelta s δ := by
  obtain ⟨hss, hn, -⟩ := hs
  have hcont : Continuous s := (AddMonoidHomClass.isometry_of_norm s hn).continuous
  have h2 : (2 : L) ≠ 0 := two_ne_zero
  have h2pos : 0 < ‖(2 : L)‖ := norm_pos_iff.2 h2
  have h2le : ‖(2 : L)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (1 : L) 1
    rw [one_add_one_eq_two] at this
    simpa using this
  have htr : ∀ y : L, ‖y‖ ≤ 1 → ‖y + s y‖ ≤ 1 := fun y hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy (by rw [hn]; exact hy))

  let I : Set L := {a | ∀ x : L, ‖x‖ ≤ 1 → ‖a * x + s (a * x)‖ ≤ 1}
  have h1I : (1 : L) ∈ I := fun x hx => by simpa using htr x hx
  have hclosed : IsClosed I := by
    have : I = ⋂ (x : L) (_ : ‖x‖ ≤ 1), {a : L | ‖a * x + s (a * x)‖ ≤ 1} := by
      ext a; simp [I]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    have hm : Continuous fun a : L => a * x := continuous_id.mul continuous_const
    exact (hm.add (hcont.comp hm)).norm
  obtain ⟨p, hp⟩ := NormedField.exists_one_lt_norm L
  obtain ⟨N, hNdef⟩ : ∃ N : L, N = p * s p := ⟨_, rfl⟩
  have hNfix : s N = N := by rw [hNdef, map_mul, hss, mul_comm]
  have hN1 : 1 < ‖N‖ := by
    rw [hNdef, norm_mul, hn]
    nlinarith
  have hbound : ∀ a ∈ I, ‖a‖ ≤ ‖N‖ / ‖(2 : L)‖ := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have hNle : ‖N‖ ≤ ‖N‖ / ‖(2 : L)‖ := by
      rw [le_div_iff₀ h2pos]
      nlinarith [norm_nonneg N]
    have ha1 : 1 ≤ ‖a‖ := by linarith
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near ha1 hN1
    have a0 : a ≠ 0 := by
      rintro rfl
      simp at ha1
      linarith
    have hapos : 0 < ‖a‖ := norm_pos_iff.2 a0
    have hx : ‖N ^ k / a‖ ≤ 1 := by
      rw [norm_div, norm_pow]
      exact (div_le_one hapos).2 hk1
    have h3 := ha _ hx
    have h4 : a * (N ^ k / a) = N ^ k := by field_simp
    rw [h4, map_pow, hNfix, ← two_mul, norm_mul, norm_pow] at h3
    have h5 : ‖N‖ ^ k ≤ 1 / ‖(2 : L)‖ := by
      rw [le_div_iff₀ h2pos]
      linarith
    have h6 : ‖N‖ ^ (k + 1) ≤ ‖N‖ / ‖(2 : L)‖ := by
      rw [pow_succ, div_eq_mul_one_div ‖N‖, mul_comm]
      exact mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
    linarith
  have hIc : IsCompact I :=
    (isCompact_closedBall (0 : L) (‖N‖ / ‖(2 : L)‖)).of_isClosed_subset hclosed
      (fun a ha => by simpa using hbound a ha)
  obtain ⟨δ, hδ, hmax⟩ := hIc.exists_isMaxOn ⟨1, h1I⟩ continuous_norm.continuousOn
  have hmax' : ∀ a ∈ I, ‖a‖ ≤ ‖δ‖ := fun a ha => hmax ha
  have hδ1 : 1 ≤ ‖δ‖ := by simpa using hmax' 1 h1I
  have δ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ1
    linarith
  have hδpos : 0 < ‖δ‖ := norm_pos_iff.2 δ0

  have hf : Continuous fun x : L => ‖x * δ + s (x * δ)‖ := by
    have hm : Continuous fun a : L => a * δ := continuous_id.mul continuous_const
    exact (hm.add (hcont.comp hm)).norm
  obtain ⟨x₀, hx₀, hx₀max⟩ := (isCompact_closedBall (0 : L) 1).exists_isMaxOn
    ⟨0, by simp⟩ hf.continuousOn
  have hx₀' : ‖x₀‖ ≤ 1 := by simpa using hx₀
  have hfmax : ∀ x : L, ‖x‖ ≤ 1 → ‖x * δ + s (x * δ)‖ ≤ ‖x₀ * δ + s (x₀ * δ)‖ := fun x hx =>
    hx₀max (by simpa using hx)
  obtain ⟨m, hm⟩ : ∃ m : L, m = x₀ * δ + s (x₀ * δ) := ⟨_, rfl⟩
  rw [← hm] at hfmax
  have hmfix : s m = m := by rw [hm, map_add (f := _), hss, add_comm]
  have hm1 : ‖m‖ ≤ 1 := by
    rw [hm, mul_comm]
    exact hδ x₀ hx₀'
  have hm0 : m ≠ 0 := by
    have hx : ‖δ⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hδ1
    have h3 := hfmax _ hx
    have h4 : δ⁻¹ * δ = 1 := inv_mul_cancel₀ δ0
    rw [h4, map_one, one_add_one_eq_two] at h3
    intro h
    rw [h, norm_zero] at h3
    linarith
  have hmpos : 0 < ‖m‖ := norm_pos_iff.2 hm0
  have hmeq : ‖m‖ = 1 := by
    by_contra hne
    have hlt : ‖m‖ < 1 := lt_of_le_of_ne hm1 hne
    have hI' : δ / m ∈ I := by
      intro x hx
      have h3 : δ / m * x + s (δ / m * x) = (x * δ + s (x * δ)) / m := by
        rw [map_mul, map_div₀, hmfix, map_mul]
        field_simp
      rw [h3, norm_div]
      exact (div_le_one hmpos).2 (hfmax x hx)
    have h4 := hmax' _ hI'
    rw [norm_div, div_le_iff₀ hmpos] at h4
    nlinarith
  refine ⟨δ, δ0, fun a => ⟨fun ha => hmax' a ha, fun ha x hx => ?_⟩, x₀ / m, ?_, ?_⟩
  · have h3 : a * x = δ * (a / δ * x) := by field_simp
    rw [h3]
    refine hδ _ ?_
    rw [norm_mul, norm_div]
    exact mul_le_one₀ ((div_le_one hδpos).2 ha) (norm_nonneg _) hx
  · rw [norm_div, hmeq, div_one]
    exact hx₀'
  · have h3 : x₀ / m * δ + s (x₀ / m * δ) = (x₀ * δ + s (x₀ * δ)) / m := by
      rw [map_mul, map_div₀, hmfix, map_mul]
      field_simp
    rw [h3, ← hm, div_self hm0]

theorem stDelta : StDelta := fun L _ _ _ _ s hs => exists_isDelta L s hs

end GlobalTheory.CompanionTheory.RgFl
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HenselStatement
section
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.LocalHensel

theorem stHensel_holds : StHensel := by
  intro L _ _ _ s hs c d hsc hsd hc hd
  obtain ⟨-, hn, -⟩ := hs
  have hcont : Continuous s := (AddMonoidHomClass.isometry_of_norm s hn).continuous
  have hXc : IsClosed {u : L | s u = u ∧ ‖u‖ ≤ 1} :=
    (isClosed_eq hcont continuous_id).inter (isClosed_le continuous_norm continuous_const)
  haveI : CompleteSpace {u : L | s u = u ∧ ‖u‖ ≤ 1} := hXc.completeSpace_coe
  haveI : Nonempty {u : L | s u = u ∧ ‖u‖ ≤ 1} := ⟨⟨0, map_zero s, by simp⟩⟩
  have hmaps : ∀ u : L, s u = u ∧ ‖u‖ ≤ 1 → s (-d - c * u ^ 2) = -d - c * u ^ 2 ∧
      ‖-d - c * u ^ 2‖ ≤ 1 := by
    rintro u ⟨hu, hu1⟩
    refine ⟨by simp only [map_sub, map_neg, map_mul, map_pow, hu, hsc, hsd], ?_⟩
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simpa using hd) ?_)
    rw [norm_neg, norm_mul, norm_pow]
    have h2 : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hu1
    exact mul_le_one₀ hc.le (by positivity) h2
  let F : {u : L | s u = u ∧ ‖u‖ ≤ 1} → {u : L | s u = u ∧ ‖u‖ ≤ 1} :=
    fun u => ⟨-d - c * (u : L) ^ 2, hmaps u u.2⟩
  have hF : ContractingWith ‖c‖₊ F := by
    refine ⟨by exact_mod_cast hc, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have hxy : ‖(x : L) + y‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le x.2.2 y.2.2)
    have key : (-d - c * (x : L) ^ 2) - (-d - c * (y : L) ^ 2)
        = -(c * (((x : L) + y) * ((x : L) - y))) := by ring
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    change ‖(-d - c * (x : L) ^ 2) - (-d - c * (y : L) ^ 2)‖ ≤ _
    rw [key, norm_neg, norm_mul, norm_mul, coe_nnnorm]
    have h0 : 0 ≤ ‖(x : L) - y‖ := norm_nonneg _
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left h0 hxy) (norm_nonneg _)
  have hfix := hF.fixedPoint_isFixedPt
  set u := ContractingWith.fixedPoint F hF with hu
  have hval : -d - c * (u : L) ^ 2 = u := congrArg Subtype.val hfix
  refine ⟨u, u.2.1, u.2.2, ?_⟩
  linear_combination -hval

end GlobalTheory.CompanionTheory.LocalHensel
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion
section
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

structure IsPieces {E ι : Type} [Ring E] [Fintype ι] (P : ι → E) : Prop where
  orth : ∀ i j, i ≠ j → P i * P j = 0
  idem : ∀ i, P i * P i = P i
  sum : ∑ i, P i = 1

def IsUpper {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (a : E) : Prop :=
  ∀ i j, wt j < wt i → P i * a * P j = 0

def IsLower {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (b : E) : Prop :=
  ∀ i j, wt i < wt j → P i * b * P j = 0

def IsLowerUni {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (b : E) : Prop :=
  IsLower wt P b ∧ ∀ i, P i * b * P i = P i

structure IsCongIdeal {E ι : Type} [Ring E] (J : AddSubgroup E) (P : ι → E) : Prop where
  mul_mem : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J
  left_mem : ∀ i, ∀ x ∈ J, P i * x ∈ J
  right_mem : ∀ i, ∀ x ∈ J, x * P i ∈ J
  inv : ∀ x ∈ J, ∃ y ∈ J, (1 + x) * (1 + y) = 1 ∧ (1 + y) * (1 + x) = 1

abbrev Idx (l : ℕ) := Option (Fin l ⊕ Fin l)

def wt {l : ℕ} : Idx l → ℕ
  | some (Sum.inl i) => i
  | none => l
  | some (Sum.inr i) => 2 * l - i

def rev {l : ℕ} : Idx l → Idx l
  | some (Sum.inl i) => some (Sum.inr i)
  | none => none
  | some (Sum.inr i) => some (Sum.inl i)

section Concrete

variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]

def tau {l : ℕ} (s : L →+* L) (u : Fin l → L) : Idx l → L
  | some (Sum.inl i) => u i
  | none => 1
  | some (Sum.inr i) => (s (u i))⁻¹

def hLin {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hh.1 x
  map_smul' a y := by simpa using hh.2.1 a x y

def projE {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) (i : Fin l) :
    Module.End L V := (s δ)⁻¹ • (hLin hh (f i)).smulRight (e i)

def projF {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) (i : Fin l) :
    Module.End L V := δ⁻¹ • (hLin hh (e i)).smulRight (f i)

def piece {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) :
    Idx l → Module.End L V
  | some (Sum.inl i) => projE hh δ e f i
  | none => 1 - ∑ i, (projE hh δ e f i + projF hh δ e f i)
  | some (Sum.inr i) => projF hh δ e f i

def congJ (Λ : AddSubgroup V) (π : L) : AddSubgroup (Module.End L V) where
  carrier := {g | ∀ x ∈ Λ, ∃ y ∈ Λ, g x = π • y}
  zero_mem' x _ := ⟨0, Λ.zero_mem, by simp⟩
  add_mem' {g g'} hg hg' x hx := by
    obtain ⟨y, hy, e1⟩ := hg x hx
    obtain ⟨y', hy', e2⟩ := hg' x hx
    exact ⟨y + y', Λ.add_mem hy hy', by simp [e1, e2, smul_add]⟩
  neg_mem' {g} hg x hx := by
    obtain ⟨y, hy, e1⟩ := hg x hx
    exact ⟨-y, Λ.neg_mem hy, by simp [e1]⟩

end Concrete

end GlobalTheory.CompanionTheory.Iwahori

end
end

