module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhSmall
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
private theorem expand_small {O : Type} [CommRing O] [IsLocalRing O] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (p : R →ₐ[O] R') (hs : maximalIdeal R * RingHom.ker p = ⊥) (J h Z : Matrix ι ι R)
    (hh : h.map (res O R) = 1) (hZ : Z.map p = 0) :
    (h + Z)ᵀ * J * (h + Z) = hᵀ * J * h + (Zᵀ * J + J * Z) ∧ (h + Z).map (res O R) = 1 := by
  have k : ∀ x y : R, res O R x = 0 → p y = 0 → x * y = 0 := fun x y hx hy => by
    have : x * y ∈ maximalIdeal R * RingHom.ker p :=
      Ideal.mul_mem_mul ((res_eq_zero_iff O R x).1 hx) hy
    rwa [hs, Ideal.mem_bot] at this
  have z1 : ∀ a b, p (Z a b) = 0 := fun a b => congrFun (congrFun hZ a) b
  have z2 : ∀ a b, res O R (Z a b) = 0 := fun a b => by rw [← res_map p, z1, map_zero]
  have h1 : ∀ a b, res O R ((h - 1) a b) = 0 := fun a b => by
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases e : a = b
    · subst e; simp
    · simp [one_apply_ne e]
  have K : ∀ A B : Matrix ι ι R, (∀ a b, res O R (A a b) = 0) → (∀ a b, p (B a b) = 0) →
      Aᵀ * J * B = 0 ∧ Bᵀ * J * A = 0 := fun A B hA hB => by
    constructor
    · ext a b
      simp only [Matrix.mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, k _ _ (hA _ _) (hB _ _), zero_mul]
    · ext a b
      simp only [Matrix.mul_apply, transpose_apply, Matrix.zero_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      rw [mul_right_comm, mul_comm (B _ _), k _ _ (hA _ _) (hB _ _), zero_mul]
  constructor
  · obtain ⟨e1, e2⟩ := K (h - 1) Z h1 z1
    obtain ⟨e3, -⟩ := K Z Z z2 z1
    rw [transpose_sub, transpose_one, sub_mul, sub_mul, one_mul, sub_eq_zero] at e1
    rw [mul_sub, mul_one, sub_eq_zero] at e2
    rw [transpose_add, add_mul, add_mul, mul_add, mul_add, e1, e2, e3]
    abel
  · ext a b
    have := congrFun (congrFun hh a) b
    simp only [map_apply] at this
    rw [map_apply, Matrix.add_apply, map_add (f := _), z2, add_zero, this]

open Matrix in
theorem UpperTheory.V.Alg.hh_small :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ →
      (∀ h' : Matrix ι ι R', Φ.HH h' → ∃ h : Matrix ι ι R, Φ.HH h ∧ h.map p = h') ∧
      (∀ h₁ h₂ : Matrix ι ι R, Φ.HH h₁ → Φ.HH h₂ → h₁.map p = h₂.map p → h₂ - h₁ ∈ Φ.g R) ∧
      ∀ h Y : Matrix ι ι R, Φ.HH h → Y ∈ Φ.g R → Y.map p = 0 → Φ.HH (h + Y) := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 R _ _ _ R' _ _ _ p hp hs
  refine ⟨?_, ?_, ?_⟩
  · classical
    rintro h' ⟨a1, a2, a3⟩
    choose s hs' using hp
    obtain ⟨h0, b1, b2⟩ : ∃ h0 : Matrix ι ι R, h0.map p = h' ∧ ∀ a b, Φ.blk a ≠ Φ.blk b → h0 a b = 0 := by
      refine ⟨Matrix.of fun a b => if Φ.blk a = Φ.blk b then s (h' a b) else 0, ?_, fun a b e => by simp [e]⟩
      ext a b
      by_cases e : Φ.blk a = Φ.blk b
      · simp [e, hs']
      · simp [e, a2 a b e]
    have b3 : h0.map (res O R) = 1 := by
      rw [← a3, ← b1]
      ext a b
      simp [res_map]
    have jp : (Φ.JR R).map p = Φ.JR R' := by
      ext a b
      simp [FormData.JR]
    have jb : ∀ a b, Φ.JR R a b ≠ 0 → Φ.blk b = Φ.σ (Φ.blk a) := fun a b e =>
      Φ.hblk a b fun n => e (by simp [FormData.JR, n])
    obtain ⟨K, hK⟩ : ∃ K : Matrix ι ι R, Φ.JR R * K = 1 :=
      (Φ.unit.map (algebraMap O R).mapMatrix).exists_right_inv
    obtain ⟨u, hu⟩ : ∃ u : R, 2 * u = 1 := by
      have := (h2.map (algebraMap O R)).exists_right_inv
      rwa [map_ofNat] at this
    obtain ⟨ε, hε, hε2⟩ : ∃ ε : R, (Φ.JR R)ᵀ = ε • Φ.JR R ∧ ε * ε = 1 := by
      rcases Φ.sym with e | e
      · refine ⟨1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
      · refine ⟨-1, ?_, by simp⟩
        ext a b
        have := congrFun (congrFun e a) b
        simp only [transpose_apply] at this
        simp [FormData.JR, this]
    set E := h0ᵀ * Φ.JR R * h0 - Φ.JR R with hE
    have E1 : E.map p = 0 := by
      rw [hE, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, transpose_map, b1, jp, a1, sub_self]
    have E2 : Eᵀ = ε • E := by
      rw [hE, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hε, smul_sub]
      simp [mul_assoc]
    have E3 : ∀ a b, Φ.blk b ≠ Φ.σ (Φ.blk a) → E a b = 0 := fun a b e => by
      have : Φ.JR R a b = 0 := by_contra fun n => e (jb a b n)
      rw [hE, Matrix.sub_apply, this, sub_zero]
      simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
      by_cases e1 : Φ.blk d = Φ.blk a
      · by_cases e2 : Φ.blk c = Φ.blk b
        · have : Φ.JR R d c = 0 := by_contra fun n => e (by rw [← e2, ← e1]; exact jb d c n)
          simp [this]
        · simp [b2 _ _ e2]
      · simp [b2 _ _ e1]
    set Z0 : Matrix ι ι R := K * ((-u) • E) with hZ0
    have Z1 : Φ.JR R * Z0 = (-u) • E := by rw [hZ0, ← mul_assoc, hK, one_mul]
    have Z2 : ∀ a b, p (Z0 a b) = 0 := fun a b => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hZ0, Matrix.mul_apply, map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      have : p (E c b) = 0 := congrFun (congrFun E1 c) b
      simp [this]
    let Z : Matrix ι ι R := Matrix.of fun a b => if Φ.blk a = Φ.blk b then Z0 a b else 0
    have Z3 : Z.map p = 0 := by
      ext a b
      by_cases e : Φ.blk a = Φ.blk b <;> simp [Z, e, Z2]
    have Z4 : Φ.JR R * Z = (-u) • E := by
      ext a b
      by_cases e : Φ.blk b = Φ.σ (Φ.blk a)
      · rw [← Z1, Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : Φ.blk c = Φ.blk b := by rw [e]; exact jb a c n
          simp [Z, this]
      · rw [Matrix.smul_apply, E3 a b e, smul_zero, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases n : Φ.JR R a c = 0
        · simp [n]
        · have : ¬ Φ.blk c = Φ.blk b := fun m => e (by rw [← m]; exact jb a c n)
          simp [Z, this]
    have Z5 : Zᵀ * Φ.JR R = (-u) • E := by
      have := congrArg (fun M => ε • Mᵀ) Z4
      simp only [transpose_mul, transpose_smul, hε, E2, Matrix.mul_smul, smul_smul] at this
      rw [hε2, one_smul, mul_left_comm, hε2, mul_one] at this
      exact this
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h0 Z b3 Z3
    refine ⟨h0 + Z, ⟨?_, fun a b e => by simp [Z, e, b2 a b e], c2⟩, ?_⟩
    · rw [c1, Z4, Z5, ← add_smul, show -u + -u = -1 by rw [← hu]; ring, neg_one_smul, hE]
      abel
    · rw [Matrix.map_add _ (map_add p), b1, Z3, add_zero]
  · rintro h₁ h₂ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ e
    have hZ : (h₂ - h₁).map p = 0 := by rw [Matrix.map_sub _ (map_sub p), e, sub_self]
    obtain ⟨c1, -⟩ := expand_small p hs (Φ.JR R) h₁ (h₂ - h₁) a3 hZ
    rw [add_sub_cancel, a1, b1, left_eq_add] at c1
    exact ⟨c1, fun a b n => by simp [a2 a b n, b2 a b n]⟩
  · rintro h Y ⟨a1, a2, a3⟩ ⟨b1, b2⟩ e
    obtain ⟨c1, c2⟩ := expand_small p hs (Φ.JR R) h Y a3 e
    exact ⟨by rw [c1, a1, b1, add_zero], fun a b n => by simp [a2 a b n, b2 a b n], c2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerCoef
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Classical in
private theorem wcomp_of_mem_ite {O : Type} [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X) {i j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt i) : wcomp O wt j f = if i = j then f else 0 := by
  ext n
  rw [coeff_wcomp]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    split_ifs with hn
    · rfl
    · exact (hf n hn).symm
  · rw [if_neg h, map_zero]
    split_ifs with hn
    · exact hf n (fun hi => h (hi.symm.trans hn))
    · rfl

theorem UpperTheory.V.Alg.ker_coef :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (K : Ideal A), maximalIdeal A * K = ⊥ → ∀ (W : WPres O X A) (κ : Type) [Fintype κ] (ε : κ → A) (wf : κ → X), (∀ u, ε u ∈ W.part (wf u)) → K = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) →
          ∃ co : κ → A → ResidueField O, (∀ u, ∀ x ∈ K, ∀ y ∈ K, co u (x + y) = co u x + co u y) ∧ (∀ u (a : A), ∀ x ∈ K, co u (a * x) = res O A a * co u x) ∧
            (∀ u j, j ≠ wf u → ∀ x ∈ K, x ∈ W.part j → co u x = 0) ∧ ∀ x ∈ K, ∃ a : κ → O, (∀ u, residue O (a u) = co u x) ∧ x = ∑ u, a u • ε u := by
  intro O _ _ X _ A _ _ _ K hK W κ _ ε wf hε hspan hrel
  classical
  have hεK : ∀ v, ε v ∈ K := fun v => by
    rw [hspan]
    exact Ideal.subset_span ⟨v, rfl⟩
  have hkill : ∀ (r : A) (y : A), r ∈ maximalIdeal A → y ∈ K → r * y = 0 := by
    intro r y hr hy
    have h1 := Ideal.mul_mem_mul hr hy
    rw [hK] at h1
    exact (Ideal.mem_bot).1 h1
  have hrep : ∀ x ∈ K, ∃ a : κ → O, x = ∑ v, a v • ε v := by
    intro x hx
    rw [hspan] at hx
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hx
    choose a ha using fun v => IsCO.res_surj (O := O) (r v)
    refine ⟨a, ?_⟩
    rw [← hr]
    apply Finset.sum_congr rfl
    intro v _
    have h0 := hkill _ _ (ha v) (hεK v)
    rw [smul_eq_mul, Algebra.smul_def]
    linear_combination h0
  let co : κ → A → ResidueField O := fun u x =>
    if h : ∃ a : κ → O, x = ∑ v, a v • ε v then residue O (h.choose u) else 0
  have hco : ∀ x (a : κ → O), x = ∑ v, a v • ε v → ∀ u, co u x = residue O (a u) := by
    intro x a hx u
    have h : ∃ a : κ → O, x = ∑ v, a v • ε v := ⟨a, hx⟩
    simp only [co]
    rw [dite_eq_left h]
    have hd : ∑ v, (h.choose v - a v) • ε v = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h.choose_spec, ← hx, sub_self]
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (hrel _ hd u)
  refine ⟨co, ?_, ?_, ?_, ?_⟩
  · intro u x hx y hy
    obtain ⟨a, ha⟩ := hrep x hx
    obtain ⟨b, hb⟩ := hrep y hy
    have hxy : x + y = ∑ v, (a + b) v • ε v := by
      rw [ha, hb, ← Finset.sum_add_distrib]
      simp only [Pi.add_apply, add_smul]
    rw [hco _ _ hxy u, hco _ _ ha u, hco _ _ hb u, Pi.add_apply, map_add (f := _)]
  · intro u a x hx
    obtain ⟨b, hb⟩ := hrep x hx
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have hax : a * x = ∑ v, (c * b v) • ε v := by
      have h0 := hkill _ _ hc hx
      have h1 : a * x = algebraMap O A c * x := by linear_combination h0
      rw [h1, hb, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [mul_smul, ← Algebra.smul_def]
    have hr : res O A a = residue O c := by
      have h1 := (res_eq_zero_iff O A _).2 hc
      rw [map_sub, sub_eq_zero, AlgHom.commutes] at h1
      rw [h1]
      rfl
    rw [hco _ _ hax u, hco _ _ hb u, map_mul, hr]
  · intro u j hj x hxK hxP
    obtain ⟨a, ha⟩ := hrep x hxK
    rw [hco x a ha u]
    apply (IsLocalRing.residue_eq_zero_iff _).2
    have hε' : ∀ v, ε v ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt (wf v)) := hε
    choose f hf hfε using fun v => Submodule.mem_map.1 (hε' v)
    have hxP' : x ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt j) := hxP
    obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.1 hxP'
    simp only [AlgHom.toLinearMap_apply] at hfε hgx
    have hk : g - ∑ v, a v • f v ∈ RingHom.ker W.π := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, map_sub, map_sum]
      simp only [map_smul, hfε]
      rw [hgx, ← ha, sub_self]
    have hh := W.homog _ hk (wf u)
    have hfw : ∀ v, wcomp O W.wt (wf u) (f v) = if wf v = wf u then f v else 0 :=
      fun v => wcomp_of_mem_ite W.wt (hf v)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, wcomp_of_mem_ite W.wt hg, if_neg hj] at hh
    simp only [map_smul, hfw] at hh
    have hrel0 : ∑ v, (if wf v = wf u then a v else 0) • ε v = 0 := by
      have h2 := RingHom.mem_ker.1 hh
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_zero, map_sum, zero_sub, neg_eq_zero] at h2
      rw [← h2]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs with hv
      · rw [map_smul, hfε]
      · rw [smul_zero, map_zero, zero_smul]
    have h5 := hrel _ hrel0 u
    simpa using h5
  · intro x hx
    obtain ⟨a, ha⟩ := hrep x hx
    exact ⟨a, fun u => (hco x a ha u).symm, ha⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem ker_gen_closed {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A)
    (f : A) (h : ∀ N : ℕ, ∃ g ∈ I, f - g ∈ maximalIdeal A ^ N) : f ∈ I := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ I) (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  have hmem : Ideal.Quotient.mk I f ∈ ⨅ i, (maximalIdeal A) ^ i • (⊤ : Submodule A (A ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro N
    obtain ⟨g, hg, hfg⟩ := h N
    have heq : Ideal.Quotient.mk I f = (f - g) • (1 : A ⧸ I) := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, map_sub,
        Ideal.Quotient.eq_zero_iff_mem.mpr hg, sub_zero]
    rw [heq]
    exact Submodule.smul_mem_smul hfg Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

private theorem ker_gen_approx {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X]
    {σ : Type} [Finite σ] (wt : σ → X) (f : MvPowerSeries σ O) (N : ℕ) :
    ∃ T : Finset X, f - ∑ j ∈ T, wcomp O wt j f ∈ maximalIdeal (MvPowerSeries σ O) ^ N := by
  classical
  set D := (Finsupp.finite_of_degree_lt (σ := σ) N).toFinset with hD
  refine ⟨D.image (Finsupp.weight wt), ?_⟩
  have hX : ∀ i : σ, (AlgHom.id O (MvPowerSeries σ O)) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries σ O) := by
    intro i
    rw [AlgHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hord : ((N : ℕ) : ℕ∞) ≤ (f - ∑ j ∈ D.image (Finsupp.weight wt), wcomp O wt j f).order := by
    apply MvPowerSeries.nat_le_order
    intro d hd
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq, if_pos, sub_self]
    exact Finset.mem_image_of_mem _ (by simpa [hD] using hd)
  have key := GlobalTheory.algHom_mem_pow_of_le_order (AlgHom.id O (MvPowerSeries σ O)) hX hord
  simpa using key

theorem UpperTheory.V.Alg.ker_gen :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] (σ : Type) [Finite σ] (wt : σ → X) (J : Ideal (MvPowerSeries σ O)), IsHomog O wt J →
      ∃ (n : ℕ) (f : Fin n → MvPowerSeries σ O) (c : Fin n → X), (∀ i, f i ∈ wtPart O wt (c i)) ∧ J = Ideal.span (Set.range f) := by
  intro O _ _ _ _ X _ σ _ wt J hJ
  classical
  set G : Set (MvPowerSeries σ O) := {g | ∃ f ∈ J, ∃ j : X, g = wcomp O wt j f} with hG
  have hGJ : Ideal.span G ≤ J := by
    rw [Ideal.span_le]
    rintro g ⟨f, hf, j, rfl⟩
    exact hJ f hf j
  have hJG : J ≤ Ideal.span G := by
    intro f hf
    apply ker_gen_closed (Ideal.span G) f
    intro N
    obtain ⟨T, hT⟩ := ker_gen_approx wt f N
    exact ⟨_, Ideal.sum_mem _ (fun j _ => Ideal.subset_span ⟨f, hf, j, rfl⟩), hT⟩
  have hfg : (Submodule.span (MvPowerSeries σ O) G).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  have hchoice : ∀ g : s, ∃ j : X, g.1 ∈ wtPart O wt j := by
    rintro ⟨g, hg⟩
    obtain ⟨f, _, j, rfl⟩ := hsG hg
    exact ⟨j, wcomp_mem O wt j f⟩
  choose c hc using hchoice
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => c (s.equivFin.symm i), fun i => hc _, ?_⟩
  have hrange : Set.range (fun i => (s.equivFin.symm i).1) = (s : Set (MvPowerSeries σ O)) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hg
      exact ⟨s.equivFin ⟨g, hg⟩, by simp⟩
  rw [hrange]
  calc J = Ideal.span G := le_antisymm hJG hGJ
    _ = Ideal.span (s : Set (MvPowerSeries σ O)) := hspan
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TactVanish
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem tact_prod {X σ S : Type} [AddCommGroup X] [CommRing S] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (x : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i k => ((t (Multiplicative.ofAdd (wt i)) : S) * x i) ^ k) =
      (t (Multiplicative.ofAdd (Finsupp.weight wt d)) : S) * d.prod fun i k => x i ^ k := by
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum, ofAdd_sum, map_prod, Units.coe_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]

private theorem tact_aeval {O X σ S : Type} [CommRing O] [AddCommGroup X] [CommRing S] [Algebra O S]
    (wt : σ → X) (t : Multiplicative X →* Sˣ) (x : σ → S) (j : X) (p : MvPolynomial σ O)
    (hp : ∀ d, Finsupp.weight wt d ≠ j → AddMonoidAlgebra.coeff p d = 0) :
    MvPolynomial.aeval (fun i => (t (Multiplicative.ofAdd (wt i)) : S) * x i) p =
      (t (Multiplicative.ofAdd j) : S) * MvPolynomial.aeval x p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [p.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : Finsupp.weight wt d = j := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hd (hp d h)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, tact_prod, hd']
  ring

private theorem tact_approx {O X σ : Type} [CommRing O] [AddCommGroup X] [Finite σ] (wt : σ → X)
    (F : MvPowerSeries σ O) (n : ℕ) :
    ∃ s : Finset X, (n : ℕ∞) ≤ (F - ∑ j ∈ s, wcomp O wt j F).order := by
  classical
  refine ⟨(truncTotal n F).support.image (Finsupp.weight wt), nat_le_order fun d hd => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra h0
    refine h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 ?_))
    rwa [coeff_truncTotal _ hd]

private theorem tact_vanish {O X σ S : Type} [CommRing O] [AddCommGroup X] [Finite σ] [CommRing S]
    [Algebra O S] (wt : σ → X) (J : Ideal S) [IsHausdorff J S] (φ : MvPowerSeries σ O →ₐ[O] S)
    (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ J) (F : MvPowerSeries σ O) (h : ∀ j, φ (wcomp O wt j F) = 0) :
    φ F = 0 := by
  apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow J
  intro n
  obtain ⟨s, hs⟩ := tact_approx wt F n
  have hm := GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum] at hm
  simpa [h] using hm

theorem UpperTheory.V.Alg.tact :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ),
      ∃! f' : R →ₐ[O] R', ∀ j, ∀ x ∈ W.part j, f' x = t (Multiplicative.ofAdd j) * f x := by
  intro O _ _ X _ R _ _ _ W hz R' _ _ _ f t
  classical
  haveI : Fintype W.σ := W.fin
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := O)
  have hf_max : ∀ x ∈ maximalIdeal R, f x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R' (f x), UpperTheory.V.Alg.res_map f x, res_eq_zero_iff O R x]
    exact hx
  let xs : W.σ → R' := fun i =>
    (t (Multiplicative.ofAdd (W.wt i)) : R') * f (W.π (MvPowerSeries.X i))
  have hxs : ∀ i, xs i ∈ maximalIdeal R' := fun i => Ideal.mul_mem_left _ _ (hf_max _ (hz i))
  obtain ⟨Ψ, hΨX, hΨtr⟩ : ∃ Ψ : MvPowerSeries W.σ O →ₐ[O] R', (∀ i, Ψ (MvPowerSeries.X i) = xs i) ∧
      ∀ (n : ℕ) (G : MvPowerSeries W.σ O),
        Ψ G - MvPolynomial.aeval xs (truncTotal n G) ∈ maximalIdeal R' ^ n :=
    ⟨_, GlobalTheory.mvEvalAdic_X _ xs hxs, GlobalTheory.mvEvalAdic_sub_aeval_truncTotal_mem _ xs hxs⟩
  have key : ∀ j, ∀ G ∈ wtPart O W.wt j,
      Ψ G = (t (Multiplicative.ofAdd j) : R') * f (W.π G) := by
    intro j G hG
    apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow (maximalIdeal R')
    intro n
    have h1 := hΨtr n G
    have h2 := GlobalTheory.algHom_sub_aeval_truncTotal_mem (f.comp W.π) (J := maximalIdeal R')
      (fun i => hf_max _ (hz i)) n G
    simp only [AlgHom.coe_comp, Function.comp_apply] at h2
    have h3 : MvPolynomial.aeval xs (truncTotal n G) =
        (t (Multiplicative.ofAdd j) : R') *
          MvPolynomial.aeval (fun i => f (W.π (MvPowerSeries.X i))) (truncTotal n G) := by
      refine tact_aeval W.wt t (fun i => f (W.π (MvPowerSeries.X i))) j _ fun d hd => ?_
      rw [coeff_truncTotal_eq_ite]
      split_ifs
      · exact hG d hd
      · rfl
    have he : Ψ G - (t (Multiplicative.ofAdd j) : R') * f (W.π G) =
        (Ψ G - MvPolynomial.aeval xs (truncTotal n G)) -
          (t (Multiplicative.ofAdd j) : R') *
            (f (W.π G) - MvPolynomial.aeval (fun i => f (W.π (MvPowerSeries.X i))) (truncTotal n G)) := by
      rw [h3]
      ring
    rw [he]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ h2)
  have hker : ∀ F ∈ RingHom.ker W.π, Ψ F = 0 := by
    intro F hF
    refine tact_vanish W.wt (maximalIdeal R') Ψ (fun i => by rw [hΨX]; exact hxs i) F fun j => ?_
    rw [key j _ (wcomp_mem O W.wt j F)]
    have h0 : W.π (wcomp O W.wt j F) = 0 := RingHom.mem_ker.mp (W.homog F hF j)
    rw [h0, map_zero, mul_zero]
  let f' : R →ₐ[O] R' := (Ideal.Quotient.liftₐ (RingHom.ker W.π) Ψ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom
  have hf'π : ∀ G, f' (W.π G) = Ψ G := by
    intro G
    have hs : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π G) =
        Ideal.Quotient.mk (RingHom.ker W.π) G := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker W.π) Ψ hker
      ((Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π G)) = Ψ G
    rw [hs]
    rfl
  refine ⟨f', ?_, ?_⟩
  · intro j x hx
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hx
    simp only [AlgHom.toLinearMap_apply]
    rw [hf'π, key j G hG]
  · intro g hg
    have hgz : ∀ i, g (W.π (MvPowerSeries.X i)) = xs i := fun i => hg (W.wt i) (W.z i) (W.z_mem i)
    have hcomp : g.comp W.π = Ψ := by
      apply GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal R')
      · intro i
        rw [AlgHom.comp_apply, hgz]
        exact hxs i
      · intro i
        rw [AlgHom.comp_apply, hgz, hΨX]
    ext x
    obtain ⟨G, rfl⟩ := W.surj x
    rw [hf'π, ← AlgHom.comp_apply, hcomp]
end

