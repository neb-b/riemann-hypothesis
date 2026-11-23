module

public import Mathlib
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0002

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLower
section
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.Unitary

variable {E ι : Type} [Ring E] [Fintype ι]

theorem piece_mul_mul {P : ι → E} (hP : IsPieces P) (x y : E) (i j : ι) :
    P i * (x * y) * P j = ∑ k, (P i * x * P k) * (P k * y * P j) := by
  have h : x * y = ∑ k, x * P k * y := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP.sum, mul_one]
  rw [h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hP.idem k
  calc P i * (x * P k * y) * P j = P i * x * P k * y * P j := by simp only [mul_assoc]
    _ = P i * x * (P k * P k) * y * P j := by rw [hk]
    _ = _ := by simp only [mul_assoc]

theorem upper_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) {x y : E}
    (hx : IsUpper wt P x) (hy : IsUpper wt P y) : IsUpper wt P (x * y) := by
  intro i j hij
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (wt k) (wt i) with h | h
  · rw [hx i k h, zero_mul]
  · rw [hy k j (lt_of_lt_of_le hij h), mul_zero]

theorem lower_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) {x y : E}
    (hx : IsLower wt P x) (hy : IsLower wt P y) : IsLower wt P (x * y) := by
  intro i j hij
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (wt i) (wt k) with h | h
  · rw [hx i k h, zero_mul]
  · rw [hy k j (lt_of_le_of_lt h hij), mul_zero]

theorem diag_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {x y : E} (hx : IsLower wt P x) (hy : IsLower wt P y) (i : ι) :
    P i * (x * y) * P i = (P i * x * P i) * (P i * y * P i) := by
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_trichotomy (wt i) (wt k) with h | h | h
  · rw [hx i k h, zero_mul]
  · exact absurd (hw h).symm hk
  · rw [hy k i h, mul_zero]

theorem lowerUni_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {x y : E} (hx : IsLowerUni wt P x) (hy : IsLowerUni wt P y) : IsLowerUni wt P (x * y) :=
  ⟨lower_mul hP hx.1 hy.1, fun i => by
    rw [diag_mul hP hw hx.1 hy.1, hx.2, hy.2, hP.idem]⟩

theorem lowerUni_of_inv {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {b b' : E} (hb : IsLowerUni wt P b) (hb' : IsLower wt P b') (h : b * b' = 1) :
    IsLowerUni wt P b' := by
  refine ⟨hb', fun i => ?_⟩
  have h1 := diag_mul hP hw hb.1 hb' i
  rw [h, mul_one, hP.idem, hb.2] at h1
  calc P i * b' * P i = P i * (P i * b' * P i) := by simp only [← mul_assoc, hP.idem]
    _ = P i := h1.symm

theorem eq_one_of_upper_lowerUni {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P)
    (hw : Function.Injective wt) {c : E} (hu : IsUpper wt P c) (hl : IsLowerUni wt P c) :
    c = 1 := by
  have h : c = ∑ i, ∑ j, P i * c * P j := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hP.sum, mul_one, one_mul]
  rw [h, ← hP.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_eq_single i (fun j _ hj => ?_)
    (fun h => absurd (Finset.mem_univ i) h)).trans (hl.2 i)
  rcases lt_trichotomy (wt i) (wt j) with h | h | h
  · exact hl.1 i j h
  · exact absurd (hw h).symm hj
  · exact hu i j h

section Anti

variable {wt : ι → ℕ} {P : ι → E} {rev : ι → ι} {st : E → E}

theorem st_block (hrev : ∀ i, rev (rev i) = i) (hmul : ∀ a b, st (a * b) = st b * st a)
    (hst : ∀ i, st (P i) = P (rev i)) (x : E) (i j : ι) :
    P i * st x * P j = st (P (rev j) * x * P (rev i)) := by
  rw [hmul, hmul, hst, hst, hrev, hrev, mul_assoc]

theorem st_upper (hrev : ∀ i, rev (rev i) = i) (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsUpper wt P x) : IsUpper wt P (st x) := by
  intro i j hij
  rw [st_block hrev hmul hst, hx (rev j) (rev i) (hord j i hij), h0]

theorem st_lower (hrev : ∀ i, rev (rev i) = i) (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsLower wt P x) : IsLower wt P (st x) := by
  intro i j hij
  rw [st_block hrev hmul hst, hx (rev j) (rev i) (hord i j hij), h0]

theorem st_lowerUni (hrev : ∀ i, rev (rev i) = i)
    (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsLowerUni wt P x) :
    IsLowerUni wt P (st x) :=
  ⟨st_lower hrev hord hmul h0 hst hx.1, fun i => by
    rw [st_block hrev hmul hst, hx.2, hst, hrev]⟩

end Anti

theorem st_mul_self_of_factor : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ (rev : ι → ι), (∀ i, rev (rev i) = i) → (∀ i j, wt i < wt j → wt (rev j) < wt (rev i)) → Function.Injective wt → ∀ (st : E → E), (∀ a b, st (a * b) = st b * st a) → st 1 = 1 → st 0 = 0 → (∀ i, st (P i) = P (rev i)) → (∀ a a' : E, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a') → (∀ b b' : E, b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b') → ∀ a a' b b' : E, a * a' = 1 → a' * a = 1 → b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b → st (a * b) * (a * b) = 1 → (a * b) * st (a * b) = 1 → st a * a = 1 ∧ st b * b = 1 := by
  intro E ι _ _ wt P hP rev hrev hord hw st hmul h1 h0 hst hU hL a a' b b' haa' ha'a hbb' hb'b ha hb hs hs'
  have ha'U : IsUpper wt P a' := hU a a' haa' ha'a ha
  have hb'Uni : IsLowerUni wt P b' := lowerUni_of_inv hP hw hb (hL b b' hbb' hb'b hb.1) hbb'
  have ha2U : IsUpper wt P (st a') := st_upper hrev hord hmul h0 hst ha'U
  have hstb : IsLowerUni wt P (st b) := st_lowerUni hrev hord hmul h0 hst hb

  have e1 : st a * st a' = 1 := by rw [← hmul, ha'a, h1]
  have e2 : st b' * st b = 1 := by rw [← hmul, hbb', h1]
  have e3 : st b * st b' = 1 := by rw [← hmul, hb'b, h1]

  have e4 : st a' * st b' = a * b := by
    have h2 : st (a * b) * (st a' * st b') = 1 := by
      rw [hmul a b, mul_assoc (st b), ← mul_assoc (st a), e1, one_mul, e3]
    calc st a' * st b' = (a * b) * st (a * b) * (st a' * st b') := by rw [hs', one_mul]
      _ = a * b := by rw [mul_assoc, h2, mul_one]
  have e5 : st a' = a * b * st b := by
    rw [← e4, mul_assoc, e2, mul_one]

  have e6 : a' * st a' = b * st b := by
    have h3 : a' * (a * b * st b) = (a' * a) * b * st b := by simp only [mul_assoc]
    rw [e5, h3, ha'a, one_mul]
  have hc : a' * st a' = 1 :=
    eq_one_of_upper_lowerUni hP hw (upper_mul hP ha'U ha2U)
      (e6 ▸ lowerUni_mul hP hw hb hstb)
  have e7 : st a' = a := by
    calc st a' = a * a' * st a' := by rw [haa', one_mul]
      _ = a := by rw [mul_assoc, hc, mul_one]
  have e8 : st b' = b := by
    have : a * st b' = a * b := by rw [← e4, e7]
    calc st b' = a' * a * st b' := by rw [ha'a, one_mul]
      _ = a' * a * b := by rw [mul_assoc, this, mul_assoc]
      _ = b := by rw [ha'a, one_mul]
  rw [e7] at e1
  rw [e8] at e3
  exact ⟨e1, e3⟩

end GlobalTheory.CompanionTheory.Iwahori.Unitary
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExists
section
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.CongUnit

variable {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
  [Module L V]

theorem norm_one_add_of_lt {t : L} (ht : ‖t‖ < 1) : ‖1 + t‖ = 1 := by
  have hne : ‖(1 : L)‖ ≠ ‖t‖ := by rw [norm_one]; exact ht.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
  exact max_eq_left ht.le

theorem exists_coord {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hx : x ≠ 0) :
    ∃ i, (∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖) ∧ b.repr x i ≠ 0 ∧
      ‖b.repr ((1 + g) x) i‖ = ‖b.repr x i‖ := by
  have hne : ∃ j, b.repr x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have : b.repr x = 0 := by
      ext j
      simpa using hcon j
    simpa using this
  obtain ⟨j₀, hj₀⟩ := hne
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖b.repr x j‖)
    ⟨j₀, Finset.mem_univ _⟩
  have hmax : ∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖ := fun j => hi j (Finset.mem_univ _)
  have hc : b.repr x i ≠ 0 := by
    intro h0
    have := hmax j₀
    rw [h0, norm_zero] at this
    exact hj₀ (norm_le_zero_iff.mp this)
  refine ⟨i, hmax, hc, ?_⟩
  set c := b.repr x i with hcdef
  have hy : c⁻¹ • x ∈ Λ := by
    rw [hb]
    intro j
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hmax j) (norm_nonneg _)
  obtain ⟨z, hz, hgz⟩ := hg _ hy
  have hzi : ‖b.repr z i‖ ≤ 1 := (hb z).1 hz i
  have hval : g x = c • π • z := by
    have h1 : g (c⁻¹ • x) = c⁻¹ • g x := map_smul g _ _
    rw [h1] at hgz
    rw [← hgz, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hGx : b.repr ((1 + g) x) i = c * (1 + π * b.repr z i) := by
    have : (1 + g) x = x + c • π • z := by
      rw [LinearMap.add_apply, Module.End.one_apply, hval]
    rw [this, map_add (f := _), map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, ← hcdef]
    ring
  have ht : ‖π * b.repr z i‖ < 1 := by
    rw [norm_mul]
    calc ‖π‖ * ‖b.repr z i‖ ≤ ‖π‖ * 1 := by gcongr
      _ < 1 := by simpa using hπ
  rw [hGx, norm_mul, norm_one_add_of_lt ht, mul_one]

theorem eq_zero_of_apply {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (h0 : (1 + g) x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨i, -, hc, hn⟩ := exists_coord b hb hπ hg hx
  rw [h0, map_zero, Finsupp.zero_apply, norm_zero] at hn
  exact hc (norm_eq_zero.mp hn.symm)

theorem mem_of_apply_mem {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hG : (1 + g) x ∈ Λ) : x ∈ Λ := by
  by_cases hx : x = 0
  · rw [hx]; exact Λ.zero_mem
  obtain ⟨i, hmax, -, hn⟩ := exists_coord b hb hπ hg hx
  rw [hb]
  intro j
  exact (hmax j).trans (hn ▸ (hb _).1 hG i)

theorem main : ∀ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V] (Λ : AddSubgroup V), IsLat L Λ → ∀ π : L, ‖π‖ < 1 →
    ∀ g ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, ∃ g' ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π,
      (1 + g) * (1 + g') = 1 ∧ (1 + g') * (1 + g) = 1 := by
  intro L V _ _ _ _ _ Λ hΛ π hπ g hg
  obtain ⟨m, b, hb⟩ := hΛ
  have hker : LinearMap.ker (1 + g) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact eq_zero_of_apply b hb hπ hg hx
  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_ker_eq_bot (1 + g)).2 hker
  have hGH : (1 + g) * (↑u⁻¹ : Module.End L V) = 1 := by rw [← hu]; exact u.mul_inv
  have hHG : (↑u⁻¹ : Module.End L V) * (1 + g) = 1 := by rw [← hu]; exact u.inv_mul
  set H : Module.End L V := ↑u⁻¹ with hH
  have hGHx : ∀ x, (1 + g) (H x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hGH
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHGx : ∀ x, H ((1 + g) x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hHG
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHmem : ∀ x ∈ Λ, H x ∈ Λ := fun x hx =>
    mem_of_apply_mem b hb hπ hg (by rw [hGHx]; exact hx)
  refine ⟨H - 1, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hgy⟩ := hg x hx
    refine ⟨-H y, Λ.neg_mem (hHmem y hy), ?_⟩
    have h1 : H x + H (g x) = x := by
      have := hHGx x
      rwa [LinearMap.add_apply, Module.End.one_apply, map_add] at this
    have h2 : (H - 1) x = H x - x := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [h2, smul_neg, ← map_smul, ← hgy]
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, h1, sub_self]
  · rw [add_sub_cancel]; exact hGH
  · rw [add_sub_cancel]; exact hHG

end GlobalTheory.CompanionTheory.Iwahori.CongUnit
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExists
section
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

theorem exists_adjoint_herm : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h →
    ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  intro L V _ _ _ _ s hs h hh g
  obtain ⟨hadd2, hsmul2, hsymm, hnd⟩ := hh
  have hss := hs.1
  have hadd1 : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y
    rw [hsymm y (x + x'), hadd2, map_add (f := _), ← hsymm, ← hsymm]
  have hsmul1 : ∀ (a : L) x y, h (a • x) y = s a * h x y := by
    intro a x y
    rw [hsymm y (a • x), hsmul2, map_mul, ← hsymm]

  let ψ₀ : V → Module.Dual L V := fun x =>
    { toFun := h x
      map_add' := hadd2 x
      map_smul' := fun a y => by simpa using hsmul2 a x y }
  have ψ₀_apply : ∀ x y, ψ₀ x y = h x y := fun _ _ => rfl
  let ψ : V →+ Module.Dual L V := AddMonoidHom.mk' ψ₀ (fun x x' => by
    ext y
    simp [ψ₀_apply, hadd1])
  have ψ_apply : ∀ x y, ψ x y = h x y := fun _ _ => rfl
  have ψ_smul : ∀ (a : L) x, ψ (a • x) = s a • ψ x := by
    intro a x
    ext y
    simp [ψ_apply, hsmul1]
  have ψ_inj : ∀ x, ψ x = 0 → x = 0 := by
    intro x hx
    exact hnd x (fun y => by rw [← ψ_apply, hx]; rfl)
  have ψ_inj' : ∀ x x', ψ x = ψ x' → x = x' := by
    intro x x' hxx
    exact sub_eq_zero.mp (ψ_inj _ (by rw [map_sub, hxx, sub_self]))

  let b := Module.finBasis L V
  have hli : LinearIndependent L (fun i => ψ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ψ (∑ j, s (c j) • b j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ψ_smul, hss]
    have h1 := ψ_inj _ h0
    have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
    have h3 := congrArg s h2
    rwa [hss, map_zero] at h3
  have hspan : Submodule.span L (Set.range fun i => ψ (b i)) = ⊤ := by
    refine hli.span_eq_top_of_card_eq_finrank' ?_
    rw [Subspace.dual_finrank_eq]
    simp
  have ψ_surj : ∀ f : Module.Dual L V, ∃ z, ψ z = f := by
    intro f
    have hf : f ∈ Submodule.span L (Set.range fun i => ψ (b i)) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hf
    refine ⟨∑ j, s (c j) • b j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hc]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ψ_smul, hss]
  choose z hz using fun y => ψ_surj ((ψ y).comp g)
  have hz' : ∀ y x, h (z y) x = h y (g x) := by
    intro y x
    rw [← ψ_apply, hz]
    rfl
  refine ⟨{ toFun := z, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro y y'
    apply ψ_inj'
    rw [hz, map_add (f := _), map_add (f := _), hz, hz]
    rfl
  · intro a y
    apply ψ_inj'
    rw [hz, RingHom.id_apply, ψ_smul, ψ_smul, hz]
    rfl
  · intro x y
    show h (g x) y = h x (z y)
    rw [hsymm (z y) x, hz', ← hsymm]

end GlobalTheory.CompanionTheory.Iwahori
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruence
section
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.TorusConj

theorem conj_sub_one_mem {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    {P : ι → E} (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) {J : AddSubgroup E}
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J)
    {S S' : E} {σ ρ : ι → L} (hS : ∀ i, P i * S = σ i • P i)
    (hS' : ∀ j, S' * P j = ρ j • P j) (hSS : S * S' = 1) {a : E} (ha : a - 1 ∈ J)
    (h : ∀ i j, ‖σ i * ρ j‖ ≤ 1 ∨ (i ≠ j ∧ P i * a * P j = 0)) :
    S * a * S' - 1 ∈ J := by
  have e1 : S * a * S' - 1 = ∑ i, ∑ j, P i * (S * (a - 1) * S') * P j := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [hP.sum]
    simp [mul_sub, sub_mul, hSS]
  rw [e1]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  have e2 : P i * (S * (a - 1) * S') * P j = (σ i * ρ j) • (P i * (a - 1) * P j) := by
    calc P i * (S * (a - 1) * S') * P j = (P i * S) * (a - 1) * (S' * P j) := by
          simp only [mul_assoc]
      _ = (σ i * ρ j) • (P i * (a - 1) * P j) := by
          rw [hS, hS']
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          rw [mul_comm]
  rw [e2]
  rcases h i j with hn | ⟨hij, hz⟩
  · exact hc _ hn _ (hJ.right_mem j _ (hJ.left_mem i _ ha))
  · have : P i * (a - 1) * P j = 0 := by
      rw [mul_sub, sub_mul, hz, mul_one, hP.orth i j hij, sub_zero]
    rw [this, smul_zero]
    exact J.zero_mem

theorem conj_congruence {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    (wt : ι → ℕ) (P : ι → E) (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) (J : AddSubgroup E)
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) (T T' : E) (τ : ι → L)
    (hτ : ∀ i, τ i ≠ 0) (hTT : T * T' = 1) (hTT' : T' * T = 1)
    (hl : ∀ i, T * P i = τ i • P i) (hr : ∀ i, P i * T = τ i • P i)
    (hw : ∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) (a b : E) (ha : a - 1 ∈ J) (hb : b - 1 ∈ J)
    (hU : GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a) (hL : GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b) :
    T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by
  have hl' : ∀ j, T' * P j = (τ j)⁻¹ • P j := by
    intro j
    have e : T' * (T * P j) = T' * (τ j • P j) := by rw [hl]
    rw [← mul_assoc, hTT', one_mul, mul_smul_comm] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  have hr' : ∀ j, P j * T' = (τ j)⁻¹ • P j := by
    intro j
    have e : (P j * T) * T' = (τ j • P j) * T' := by rw [hr]
    rw [mul_assoc, hTT, mul_one, smul_mul_assoc] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  constructor
  · refine conj_sub_one_mem hP hJ hc hr hl' hTT ha fun i j => ?_
    by_cases hij : wt j < wt i
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hU i j hij⟩
    · left
      have hn := hw i j (not_lt.mp hij)
      have hpos : 0 < ‖τ j‖ := norm_pos_iff.mpr (hτ j)
      rw [norm_mul, norm_inv, ← div_eq_mul_inv]
      exact (div_le_one hpos).mpr hn
  · refine conj_sub_one_mem hP hJ hc hr' hl hTT' hb fun i j => ?_
    by_cases hij : wt i < wt j
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hL i j hij⟩
    · left
      have hn := hw j i (not_lt.mp hij)
      have hpos : 0 < ‖τ i‖ := norm_pos_iff.mpr (hτ i)
      rw [norm_mul, norm_inv, inv_mul_eq_div]
      exact (div_le_one hpos).mpr hn

end GlobalTheory.CompanionTheory.Iwahori.TorusConj
end

