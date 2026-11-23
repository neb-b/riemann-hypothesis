module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRingOfIntegersLift
section
open NumberField

namespace GlobalTheory.PlaceInt


open NumberField in
theorem _root_.GlobalTheory.PlaceInt.exists_ringOfIntegers_lift (E : Type) [Field E] [NumberField E]
    (V : Type) [CommRing V]
    [IsDomain V] [IsIntegrallyClosed V] (k : Type) [Field k] [Algebra V k] [IsFractionRing V k]
    (ψ : E →+* k) :
    ∃ σ : 𝓞 E →+* V, ∀ x : 𝓞 E, algebraMap V k (σ x) = ψ (x : E) := by
  have inj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  have hint : ∀ x : 𝓞 E, ∃ y : V, algebraMap V k y = ψ (x : E) := by
    intro x
    have h1 : IsIntegral ℤ (ψ (x : E)) := x.isIntegral_coe.map ψ.toIntAlgHom
    have h2 : IsIntegral V (ψ (x : E)) := h1.tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  choose f hf using hint
  refine ⟨{ toFun := f
            map_one' := inj (by rw [hf, map_one]; simp)
            map_mul' := fun x y => inj (by rw [map_mul, hf, hf, hf]; push_cast; rw [map_mul])
            map_zero' := inj (by rw [hf, map_zero]; simp)
            map_add' := fun x y => inj (by rw [map_add (f := _), hf, hf, hf]; push_cast; rw [map_add (f := _)]) },
    hf⟩


open NumberField Polynomial IsLocalRing in
theorem _root_.GlobalTheory.PlaceInt.placeIdem : _root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.PlaceIdemSt := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.PlaceIdemSt
  intro E _ _ V _ _ _ _ k _ _ _ P hP hP0
  classical
  choose σ hσ using fun ψ : E →+* k => _root_.GlobalTheory.PlaceInt.exists_ringOfIntegers_lift E V k ψ
  have inj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  obtain ⟨Q, hQ, hQp⟩ : ∃ Q : (E →+* k) → Ideal (𝓞 E),
      (∀ ψ x, x ∈ Q ψ ↔ σ ψ x ∈ maximalIdeal V) ∧ ∀ ψ, (Q ψ).IsPrime :=
    ⟨fun ψ => (maximalIdeal V).comap (σ ψ), fun _ _ => Iff.rfl, fun _ => inferInstance⟩
  have hcond : ∀ ψ : E →+* k, (∀ x : 𝓞 E, x ∈ P ↔
      ψ (x : E) ∈ algebraMap V k '' (maximalIdeal V : Set V)) ↔ Q ψ = P := by
    intro ψ
    have key : ∀ x : 𝓞 E, ψ (x : E) ∈ algebraMap V k '' (maximalIdeal V : Set V) ↔ x ∈ Q ψ := by
      intro x
      rw [hQ, ← hσ]
      constructor
      · rintro ⟨y, hy, h⟩
        exact inj h ▸ hy
      · intro h
        exact ⟨_, h, rfl⟩
    simp only [key]
    rw [eq_comm, SetLike.ext_iff]
  by_cases hex : ∃ ψ0 : E →+* k, Q ψ0 = P
  swap
  · refine ⟨0, Fin.elim0, Fin.elim0, fun ψ => ?_⟩
    rw [if_neg (fun h => hex ⟨ψ, (hcond ψ).mp h⟩)]
    simp
  obtain ⟨ψ0, hψ0⟩ := hex
  haveI : CharZero k := ⟨fun a b h => by
    rw [← map_natCast ψ0, ← map_natCast ψ0 b] at h
    exact Nat.cast_injective (ψ0.injective h)⟩
  have hPmax : P.IsMaximal := hP.isMaximal hP0

  set N : ℕ := Ideal.absNorm P with hN
  have hNP : (N : 𝓞 E) ∈ P := Ideal.absNorm_mem P
  have hN0 : (N : 𝓞 E) ≠ 0 := by
    rw [Nat.cast_ne_zero, hN]
    exact fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hNQ : ∀ ψ, (N : 𝓞 E) ∈ Q ψ := by
    intro ψ
    have h0 : (N : 𝓞 E) ∈ Q ψ0 := hψ0 ▸ hNP
    rw [hQ, map_natCast] at h0 ⊢
    exact h0
  have hc : ∀ ψ, ∃ c : 𝓞 E, c ∉ P ∧ (Q ψ ≠ P → c ∈ Q ψ) := by
    intro ψ
    by_cases h : Q ψ = P
    · exact ⟨1, fun h1 => hPmax.ne_top ((Ideal.eq_top_iff_one _).2 h1), fun h' => (h' h).elim⟩
    · have hQ0 : Q ψ ≠ ⊥ := fun h0 => hN0 (by simpa [h0] using hNQ ψ)
      have hQmax : (Q ψ).IsMaximal := (hQp ψ).isMaximal hQ0
      have hnle : ¬ Q ψ ≤ P := fun hle => h (hQmax.eq_of_le hPmax.ne_top hle)
      obtain ⟨c, hcQ, hcP⟩ := SetLike.not_le_iff_exists.mp hnle
      exact ⟨c, hcP, fun _ => hcQ⟩
  choose c hcP hcQ using hc
  have hprod : ∏ ψ, c ψ ∉ P := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨ψ, -, h⟩
    exact hcP ψ h
  obtain ⟨y, i, hi, hyi⟩ := hPmax.exists_inv hprod
  set b : 𝓞 E := y * ∏ ψ, c ψ with hb
  have hb1 : ∀ ψ, Q ψ = P → σ ψ b - 1 ∈ maximalIdeal V := by
    intro ψ h
    have : b - 1 ∈ Q ψ := by
      rw [h]
      have : b - 1 = -i := by rw [hb, ← hyi]; ring
      rw [this]
      exact P.neg_mem hi
    rw [hQ, map_sub, map_one] at this
    exact this
  have hb0 : ∀ ψ, Q ψ ≠ P → σ ψ b ∈ maximalIdeal V := by
    intro ψ h
    rw [← hQ]
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ ψ)
    rw [hb, hr]
    exact (Q ψ).mul_mem_left _ ((Q ψ).mul_mem_right _ (hcQ ψ h))

  set p0 : V[X] := ∏ ψ ∈ Finset.univ.filter (fun ψ => Q ψ ≠ P), (X - C (σ ψ b)) with hp0
  set p1 : V[X] := ∏ ψ ∈ Finset.univ.filter (fun ψ => Q ψ = P), (X - C (σ ψ b)) with hp1
  have hcop : IsCoprime p0 p1 := by
    rw [hp0, hp1]
    refine IsCoprime.prod_left fun ψ hψ => IsCoprime.prod_right fun φ hφ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ hφ
    apply isCoprime_X_sub_C_of_isUnit_sub
    have h0 := hb0 ψ hψ
    have h1 := hb1 φ hφ
    have hnot : σ ψ b - σ φ b ∉ maximalIdeal V := by
      intro h
      apply (maximalIdeal.isMaximal V).ne_top
      rw [Ideal.eq_top_iff_one]
      have := sub_mem (sub_mem h0 h) h1
      simpa using this
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hnot
  obtain ⟨u, v, huv⟩ := hcop
  set g : V[X] := u * p0 with hg
  refine ⟨g.natDegree + 1, fun j => b ^ (j : ℕ), fun j => g.coeff j, fun ψ => ?_⟩
  have hsum : ∑ j : Fin (g.natDegree + 1), algebraMap V k (g.coeff j) * ψ ((b ^ (j : ℕ) : 𝓞 E) : E)
      = algebraMap V k (g.eval (σ ψ b)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eval_eq_sum_range' (Nat.lt_succ_self _), map_sum,
      ← Fin.sum_univ_eq_sum_range (fun j => algebraMap V k (g.coeff j * σ ψ b ^ j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hσ]
    simp only [map_pow, map_mul]
  rw [hsum]
  by_cases h : Q ψ = P
  · rw [if_pos ((hcond ψ).mpr h)]
    have hp1z : p1.eval (σ ψ b) = 0 := by
      rw [hp1, eval_prod]
      exact Finset.prod_eq_zero (i := ψ) (by simp [h]) (by simp)
    have : g.eval (σ ψ b) = 1 := by
      have h2 : (u * p0 + v * p1).eval (σ ψ b) = 1 := by rw [huv, eval_one]
      rw [eval_add, show (v * p1).eval (σ ψ b) = 0 by rw [eval_mul, hp1z, mul_zero],
        add_zero] at h2
      exact h2
    rw [this, map_one]
  · rw [if_neg (fun h' => h ((hcond ψ).mp h'))]
    have hp0z : p0.eval (σ ψ b) = 0 := by
      rw [hp0, eval_prod]
      exact Finset.prod_eq_zero (i := ψ) (by simp [h]) (by simp)
    rw [hg, eval_mul, hp0z, mul_zero, map_zero]

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalMulN

open GlobalTheory.GaugeAdjoint

variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)

theorem const_three {x y z : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hz : ∀ i, constantCoeff (z i) = 0) (j : Fin 3)
    (i : Fin d) : constantCoeff ((![x, y, z] : Fin 3 → Pt R n d) j i) = 0 := by
  fin_cases j
  · exact hx i
  · exact hy i
  · exact hz i

theorem ev_pt_fun {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m) :
    (fun i => ev a (pt R d j i)) = a j := by
  funext i
  exact ev_pt ha j i

theorem ev_zero_fun {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    (fun i => ev a ((0 : Pt R m d) i)) = 0 := by
  funext i
  exact ev_zero ha

theorem const_add {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (i : Fin d) : constantCoeff (G.add x y i) = 0 := by
  show constantCoeff (ev ![x, y] (G.F i)) = 0
  rw [constantCoeff_ev (const_two hx hy)]
  exact G.const i

theorem ev_add_pts {x y : Pt R m d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) {b : Fin m → Pt R n d}
    (hb : ∀ j i, constantCoeff (b j i) = 0) :
    (fun i => ev b (G.add x y i)) = G.add (fun i => ev b (x i)) (fun i => ev b (y i)) := by
  funext i
  exact ev_ev_two hx hy hb (G.F i)

theorem zero_add_pt {y : Pt R n d} (hy : ∀ i, constantCoeff (y i) = 0) : G.add 0 y = y := by
  have hu : G.add 0 (pt R (n := 1) d 0) = pt R (n := 1) d 0 := funext fun i => G.unit i
  have h : (fun i => ev ![y] (G.add 0 (pt R (n := 1) d 0) i)) =
      fun i => ev ![y] (pt R (n := 1) d 0 i) := by rw [hu]
  rw [ev_add_pts G const_zero (const_pt 0) (const_one hy), ev_zero_fun (const_one hy),
    ev_pt_fun (const_one hy) 0] at h
  exact h

theorem add_comm_pt {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) : G.add x y = G.add y x := by
  have hc : G.add (pt R (n := 2) d 1) (pt R (n := 2) d 0) = G.F := funext fun i => G.comm i
  have h : (fun i => ev ![x, y] (G.add (pt R (n := 2) d 1) (pt R (n := 2) d 0) i)) =
      fun i => ev ![x, y] (G.F i) := by rw [hc]
  rw [ev_add_pts G (const_pt 1) (const_pt 0) (const_two hx hy), ev_pt_fun (const_two hx hy) 1,
    ev_pt_fun (const_two hx hy) 0] at h
  exact h.symm

theorem add_zero_pt {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) : G.add x 0 = x := by
  rw [add_comm_pt G hx const_zero]
  exact zero_add_pt G hx

theorem add_assoc_pt {x y z : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hz : ∀ i, constantCoeff (z i) = 0) :
    G.add (G.add x y) z = G.add x (G.add y z) := by
  have h3 := const_three hx hy hz
  have hA : G.add (G.add (pt R (n := 3) d 0) (pt R d 1)) (pt R d 2) =
      G.add (pt R (n := 3) d 0) (G.add (pt R d 1) (pt R d 2)) := funext fun i => G.assoc i
  have h : (fun i => ev ![x, y, z] (G.add (G.add (pt R (n := 3) d 0) (pt R d 1)) (pt R d 2) i)) =
      fun i => ev ![x, y, z] (G.add (pt R (n := 3) d 0) (G.add (pt R d 1) (pt R d 2)) i) := by
    rw [hA]
  rw [ev_add_pts G (const_add G (const_pt 0) (const_pt 1)) (const_pt 2) h3,
    ev_add_pts G (const_pt 0) (const_add G (const_pt 1) (const_pt 2)) h3,
    ev_add_pts G (const_pt 0) (const_pt 1) h3, ev_add_pts G (const_pt 1) (const_pt 2) h3,
    ev_pt_fun h3 0, ev_pt_fun h3 1, ev_pt_fun h3 2] at h
  exact h

theorem add_add_add_comm_pt {x y z w : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hz : ∀ i, constantCoeff (z i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    G.add (G.add x y) (G.add z w) = G.add (G.add x z) (G.add y w) := by
  rw [add_assoc_pt G hx hy (const_add G hz hw), ← add_assoc_pt G hy hz hw, add_comm_pt G hy hz,
    add_assoc_pt G hz hy hw, ← add_assoc_pt G hx hz (const_add G hy hw)]

theorem const_mulN (k : ℕ) : ∀ i, constantCoeff (mulN G k i) = 0 := by
  induction k with
  | zero => intro i; exact const_zero i
  | succ k ih => intro i; exact const_add G ih (const_pt 0) i

theorem formalGroupLaw_comp_mulN_zero {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    comp1 (mulN G 0) x = 0 := by
  exact ev_zero_fun (const_one hx)

theorem formalGroupLaw_comp_mulN_succ (k : ℕ) {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    comp1 (mulN G (k + 1)) x = G.add (comp1 (mulN G k) x) x := by
  show (fun i => ev ![x] (G.add (mulN G k) (pt R d 0) i)) = _
  rw [ev_add_pts G (const_mulN G k) (const_pt 0) (const_one hx), ev_pt_fun (const_one hx) 0]
  rfl

theorem formalGroupLaw_comp_mulN_add (k : ℕ) {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) :
    comp1 (mulN G k) (G.add x y) = G.add (comp1 (mulN G k) x) (comp1 (mulN G k) y) := by
  induction k with
  | zero =>
    rw [formalGroupLaw_comp_mulN_zero G (const_add G hx hy), formalGroupLaw_comp_mulN_zero G hx, formalGroupLaw_comp_mulN_zero G hy,
      zero_add_pt G const_zero]
  | succ k ih =>
    rw [formalGroupLaw_comp_mulN_succ G k (const_add G hx hy), ih, formalGroupLaw_comp_mulN_succ G k hx,
      formalGroupLaw_comp_mulN_succ G k hy,
      add_add_add_comm_pt G (const_comp1 (const_mulN G k) hx) (const_comp1 (const_mulN G k) hy) hx hy]

theorem coeff_single_one {σ : Type} (s : σ) (f : MvPowerSeries σ R) :
    coeff (Finsupp.single s 1) f = constantCoeff (pderiv s f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem lin_ev_two {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (f : PS R 2 d) (s : Fin n × Fin d) :
    coeff (Finsupp.single s 1) (ev ![x, y] f) =
      ∑ l, coeff (Finsupp.single ((0 : Fin 2), l) 1) f * coeff (Finsupp.single s 1) (x l) +
      ∑ l, coeff (Finsupp.single ((1 : Fin 2), l) 1) f * coeff (Finsupp.single s 1) (y l) := by
  have ha := const_two hx hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_single_one s (ev ![x, y] f), pderiv_ev ha, map_sum, Fin.sum_univ_two]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, constantCoeff_ev ha, ← coeff_single_one, Matrix.cons_val_zero,
    Matrix.cons_val_one]

private lemma coeff_single_pt_eq_ite (j j' : Fin n) (l l' : Fin d) :
    coeff (Finsupp.single (j', l') 1) (pt R d j l) = if j = j' ∧ l = l' then 1 else 0 := by
  show coeff _ (X (j, l)) = _
  rw [coeff_X]
  by_cases h : j = j' ∧ l = l'
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    have h2 := Finsupp.single_left_injective one_ne_zero h'
    simp only [Prod.mk.injEq] at h2
    exact h ⟨h2.1.symm, h2.2.symm⟩

theorem coeff_single_pt (j : Fin n) (l l' : Fin d) :
    coeff (Finsupp.single (j, l') 1) (pt R d j l) = if l = l' then 1 else 0 := by
  rw [coeff_single_pt_eq_ite]
  simp

theorem lin_F_right (i l : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), l) 1) (G.F i) = if i = l then 1 else 0 := by
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), l) 1)) (G.unit i)
  have hX : coeff (Finsupp.single ((0 : Fin 1), l) 1) (X ((0 : Fin 1), i) : PS R 1 d) =
      if i = l then 1 else 0 := coeff_single_pt 0 i l
  rw [lin_ev_two const_zero (const_pt 0), hX] at h
  simpa [coeff_single_pt] using h

private lemma coeff_single_pt_eq_ite' (j j' : Fin n) (l l' : Fin d) :
    coeff (Finsupp.single (j', l') 1) (pt R d j l) = if j = j' ∧ l = l' then 1 else 0 := by
  show coeff _ (X (j, l)) = _
  rw [coeff_X]
  by_cases h : j = j' ∧ l = l'
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    have h2 := Finsupp.single_left_injective one_ne_zero h'
    simp only [Prod.mk.injEq] at h2
    exact h ⟨h2.1.symm, h2.2.symm⟩

theorem lin_F_left (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if i = l then 1 else 0 := by
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 2), l) 1)) (G.comm i)
  rw [lin_ev_two (const_pt 1) (const_pt 0)] at h
  rw [← h]
  simp [coeff_single_pt_eq_ite', lin_F_right G]

theorem dLin_add {x y : Pt R 1 d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) : dLin (G.add x y) = dLin x + dLin y := by
  ext i j
  rw [Matrix.add_apply]
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![x, y] (G.F i)) =
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (x i) + coeff (Finsupp.single ((0 : Fin 1), j) 1) (y i)
  rw [lin_ev_two hx hy]
  simp [lin_F_left G, lin_F_right G]

theorem dLin_pt : dLin (pt R (n := 1) d 0) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  exact coeff_single_pt 0 i j

theorem dLin_mulN (k : ℕ) : dLin (mulN G k) = (k : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  induction k with
  | zero =>
    ext i j
    simp [dLin, mulN]
  | succ k ih =>
    show dLin (G.add (mulN G k) (pt R d 0)) = _
    rw [dLin_add G (const_mulN G k) (const_pt 0), ih, dLin_pt, Nat.cast_succ, add_smul, one_smul]

theorem mulN_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (n : ℕ),
    (∀ i, constantCoeff (mulN G n i) = 0) ∧
    comp1 (mulN G n) (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 (mulN G n) (pt R (n := 2) d 0)) (comp1 (mulN G n) (pt R (n := 2) d 1)) ∧
    dLin (mulN G n) = (n : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  intro R inst d G n
  exact ⟨const_mulN G n, formalGroupLaw_comp_mulN_add G n (const_pt 0) (const_pt 1), dLin_mulN G n⟩

end GlobalTheory.FormalMulN
end

