module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Sym.Sym2.Order

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemSpanX
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
open MvPowerSeries
private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf
end

private theorem der_zero {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {σ : R →ₐ[O] R} (P : GPres O σ) (D : R →ₗ[O] ResidueField O) (hD : D ∈ PtDer (res O R) (ResidueField O))
    (h : ∀ s, D (P.p (MvPowerSeries.X s)) = 0) : D = 0 := by
  have hm : ∀ f g, D (f * g) = res O R f • D g + res O R g • D f := hD
  have h1 : D 1 = 0 := by
    have := hm 1 1
    simp only [mul_one, map_one, one_smul] at this
    exact left_eq_add.1 this
  have hs : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : _ → MvPowerSeries (Fin P.a ⊕ Fin P.g) O)),
      res O R (P.p g) = 0 ∧ D (P.p g) = 0 := fun g hg => by
    refine Submodule.span_induction (p := fun g _ => res O R (P.p g) = 0 ∧ D (P.p g) = 0) ?_ (by simp) ?_ ?_ hg
    · rintro _ ⟨s, rfl⟩
      exact ⟨(res_eq_zero_iff O R _).2 (P.var s), h s⟩
    · rintro x y - - ⟨a, b⟩ ⟨c, d⟩
      simp [a, b, c, d]
    · rintro x y - ⟨a, b⟩
      rw [smul_eq_mul, map_mul, map_mul, hm, a, b]
      simp
  ext x
  obtain ⟨f, rfl⟩ := P.surj x
  have e : f = (f - algebraMap O _ (MvPowerSeries.constantCoeff f)) + (MvPowerSeries.constantCoeff f) • 1 := by
    rw [Algebra.algebraMap_eq_smul_one, sub_add_cancel]
  have h2 := (hs _ (mem_span_X (f - algebraMap O _ (MvPowerSeries.constantCoeff f))
    (by simp [MvPowerSeries.algebraMap_apply]))).2
  rw [e, map_add (f := _), map_add (f := _), h2, map_smul, map_smul, map_one, h1]
  simp

private theorem der_off {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {R : Type} [CommRing R]
    [Algebra O R] [IsCO O R] {σ : R →ₐ[O] R} (P : GPres O σ) (j : ZMod 2) (D : R →ₗ[O] ResidueField O)
    (hD : D ∈ derp O σ j) (s : Fin P.a ⊕ Fin P.g) (hs : Space.Loc.par P.a P.g s ≠ j) :
    D (P.p (MvPowerSeries.X s)) = 0 := by
  have h1 : P.p (MvPowerSeries.X s) ∈ evp σ (Space.Loc.par P.a P.g s) := by
    rw [← P.part]
    exact ⟨_, X_mem_wtPart O _ s, rfl⟩
  have h3 : σ (P.p (MvPowerSeries.X s)) = sg R (Space.Loc.par P.a P.g s) * P.p (MvPowerSeries.X s) := h1
  have h4 : D (σ (P.p (MvPowerSeries.X s))) = sg (ResidueField O) j * D (P.p (MvPowerSeries.X s)) := hD.2 _
  have h5 : (2 : ResidueField O) ≠ 0 := by
    have := (h2.map (residue O)).ne_zero
    rwa [map_ofNat] at this
  rw [h3] at h4
  generalize Space.Loc.par P.a P.g s = i at hs h4
  generalize P.p (MvPowerSeries.X s) = y at h4
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have hc : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  apply (mul_eq_zero.1 (show 2 * D y = 0 from ?_)).resolve_left h5
  rcases hc i with rfl | rfl <;> rcases hc j with rfl | rfl
  · exact absurd rfl hs
  · simp only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul] at h4
    linear_combination h4
  · simp only [sg, ZMod.val_zero, v1, pow_zero, pow_one, one_mul, neg_mul, map_neg] at h4
    linear_combination -h4
  · exact absurd rfl hs

private theorem der_bound {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R]
    [Algebra O R] (N : Submodule (ResidueField O) (R →ₗ[O] ResidueField O)) {ι : Type} [Fintype ι] (y : ι → R)
    (h : ∀ D ∈ N, (∀ i, D (y i) = 0) → D = 0) :
    Module.Finite (ResidueField O) N ∧ Module.finrank (ResidueField O) N ≤ Fintype.card ι := by
  let φ : N →ₗ[ResidueField O] (ι → ResidueField O) :=
    { toFun := fun D i => D.1 (y i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := (injective_iff_map_eq_zero φ).2 fun D hD =>
    Subtype.ext (h D.1 D.2 fun i => congrFun hD i)
  exact ⟨Module.Finite.of_injective φ hφ, by
    simpa using LinearMap.finrank_le_finrank_of_injective hφ⟩

theorem UpperTheory.V.Fr.ep_der :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (P : GPres O σ), (∀ j, Module.Finite (ResidueField O) (derp O σ j)) ∧ Module.finrank (ResidueField O) (derp O σ 0) ≤ P.a ∧ Module.finrank (ResidueField O) (derp O σ 1) ≤ P.g := by
  intro O _ _ _ _ h2 R _ _ _ σ P
  refine ⟨fun j => (der_bound (derp O σ j) (fun s => P.p (MvPowerSeries.X s))
    fun D hD h => der_zero P D hD.1 h).1, ?_, ?_⟩
  · have := (der_bound (derp O σ 0) (fun i : Fin P.a => P.p (MvPowerSeries.X (.inl i)))
      fun D hD h => der_zero P D hD.1 fun s => by
        rcases s with i | i
        · exact h i
        · exact der_off h2 P 0 D hD _ (show (1 : ZMod 2) ≠ 0 by decide)).2
    simpa using this
  · have := (der_bound (derp O σ 1) (fun i : Fin P.g => P.p (MvPowerSeries.X (.inr i)))
      fun D hD h => der_zero P D hD.1 fun s => by
        rcases s with i | i
        · exact der_off h2 P 1 D hD _ (show (0 : ZMod 2) ≠ 1 by decide)
        · exact h i).2
    simpa using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBdim
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private def borEquiv (K : Type) [Field K] (n : ℕ) (g : GL (Fin n) K) :
    bor g ≃ₗ[K] ({p : Fin n × Fin n // p.1 ≤ p.2} → K) where
  toFun X p := ((g : Matrix (Fin n) (Fin n) K) * X.1 * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p.1.1 p.1.2
  map_add' X Y := by
    funext p
    simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext p
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply,
      RingHom.id_apply]
  invFun f := ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0) * (g : Matrix (Fin n) (Fin n) K), by
    intro i j h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one, Matrix.of_apply, dite_eq_right (not_le.mpr h)]⟩
  left_inv X := by
    apply Subtype.ext
    have e : (Matrix.of fun i j => if i ≤ j then ((g : Matrix (Fin n) (Fin n) K) * X.1 *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j else 0) =
        (g : Matrix (Fin n) (Fin n) K) * X.1 * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      ext i j
      rw [Matrix.of_apply]
      split_ifs with h
      · rfl
      · exact (X.2 i j (not_le.mp h)).symm
    show ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if i ≤ j then ((g : Matrix (Fin n) (Fin n) K) * X.1 *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j else 0) * (g : Matrix (Fin n) (Fin n) K) = X.1
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  right_inv f := by
    funext p
    show ((g : Matrix (Fin n) (Fin n) K) * (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0) * (g : Matrix (Fin n) (Fin n) K)) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p.1.1 p.1.2 = f p
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one, Matrix.of_apply, dite_eq_left p.2]

theorem UpperTheory.V.Fr.pr_bdim :
    ∀ (K : Type) [Field K] (n : ℕ) (g : GL (Fin n) K), 2 * Module.finrank K (bor g) = n * (n + 1) := by
  intro K _ n g
  rw [(borEquiv K n g).finrank_eq, Module.finrank_fintype_fun_eq_card,
    ← Fintype.card_congr (Sym2.sortEquiv (α := Fin n)), Sym2.card, Fintype.card_fin, Nat.choose_two_right,
    Nat.add_sub_cancel, Nat.mul_comm (n + 1) n]
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBrig
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : UpT A) (hB : UpT B) :
    UpT (A * B) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge c i with hc | hc
  · rw [hA i c hc, zero_mul]
  · rw [hB c j (lt_of_lt_of_le h hc), mul_zero]

private theorem upT_of_comm {K : Type} [Field K] {n : ℕ} {T Z : Matrix (Fin n) (Fin n) K} (hT : UpT T)
    (hd : ∀ i j, i ≠ j → T i i ≠ T j j) (h : UpT (T * Z - Z * T)) : UpT Z := by
  have key : ∀ m : ℕ, ∀ i j : Fin n, n - i.val + j.val = m → j < i → Z i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i j hm hji
      have h0 := h i j hji
      have hji' : j.val < i.val := hji
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single i, Finset.sum_eq_single j] at h0
      · have h1 : (T i i - T j j) * Z i j = 0 := by linear_combination h0
        exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (hd i j hji.ne'))
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · have hc' : c.val < j.val := hc
          rw [ih (n - i.val + c.val) (by omega) i c rfl (hc.trans hji), zero_mul]
        · rw [hT c j hc, mul_zero]
      · simp
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · rw [hT i c hc, zero_mul]
        · have hc' : i.val < c.val := hc
          have := c.isLt
          rw [ih (n - c.val + j.val) (by omega) c j rfl (hji.trans hc), mul_zero]
      · simp
  exact fun i j hij => key _ i j rfl hij

theorem UpperTheory.V.Fr.pr_brig :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (K : Type) [Field K] (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.Good → ∀ (v : F.V) (Y : Matrix (Fin n) (Fin n) K), (∀ s, B.ad (F.loc v s) Y - Y ∈ B.b v) → Y ∈ B.b v := by
  intro l _ k _ F n K _ ρ B hOf hG v Y hY
  obtain ⟨s, hs⟩ := hG.ψd v
  have hT := B.tri v s
  have hr : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have hres : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := hOf.res (F.loc0 v s)
  have h1 : UpT ((B.g v : Matrix (Fin n) (Fin n) K) * ((B.r (F.loc v s)).adFun Y - Y) *
      (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := hY s
  show UpT ((B.g v : Matrix (Fin n) (Fin n) K) * Y * (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  refine upT_of_comm hT (fun i j hij => ?_) ?_
  · rw [hres, hOf.psi, hOf.psi]
    exact fun e => hs i j hij (Units.ext e)
  · convert upT_mul h1 hT using 1
    simp only [GG.adFun, hr, if_true, GG.mat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Units.inv_mul_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCfix
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem card_pairs (n : ℕ) :
    2 * Fintype.card {p : Fin n × Fin n // p.1 < p.2} + n = n * n := by
  have e : {p : Fin n × Fin n // p.1 < p.2} ≃ Σ j : Fin n, {i : Fin n // i < j} :=
    { toFun := fun p => ⟨p.1.2, p.1.1, p.2⟩
      invFun := fun q => ⟨(q.2.1, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have hc : ∀ j : Fin n, Fintype.card {i : Fin n // i < j} = j := by
    intro j
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin n => i < j) = Finset.Iio j := by
      ext i; simp
    rw [this, Fin.card_Iio]
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
  have hs := Finset.sum_range_id_mul_two n
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel] at hs
    nlinarith [hs]

private theorem finrank_skew {K : Type} [Field K] {n : ℕ} (h2 : (2 : K) ≠ 0)
    (W : Submodule K (Matrix (Fin n) (Fin n) K)) (S T : Matrix (Fin n) (Fin n) K)
    (hST : S * T = 1) (hTS : T * S = 1) (hW : ∀ X, X ∈ W ↔ (X * S)ᵀ = -(X * S)) :
    Module.finrank K W = Fintype.card {p : Fin n × Fin n // p.1 < p.2} := by
  classical
  let M : ({p : Fin n × Fin n // p.1 < p.2} → K) → Matrix (Fin n) (Fin n) K :=
    fun f => Matrix.of fun i j =>
      if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0
  have hskew : ∀ f, (M f)ᵀ = -(M f) := by
    intro f
    ext i j
    simp only [M, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    split_ifs <;> first | simp | (exfalso; omega)
  let e : W ≃ₗ[K] ({p : Fin n × Fin n // p.1 < p.2} → K) :=
    { toFun := fun X p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2
      map_add' := by
        intro X Y
        funext p
        simp [Matrix.add_mul]
      map_smul' := by
        intro c X
        funext p
        simp
      invFun := fun f => ⟨M f * T, by
        rw [hW, Matrix.mul_assoc, hTS, Matrix.mul_one]
        exact hskew f⟩
      left_inv := by
        intro X
        apply Subtype.ext
        have hX : ((X : Matrix (Fin n) (Fin n) K) * S)ᵀ = -((X : Matrix (Fin n) (Fin n) K) * S) :=
          (hW X).1 X.2
        show M (fun p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2) * T = X
        have hM : M (fun p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2)
            = (X : Matrix (Fin n) (Fin n) K) * S := by
          ext i j
          have hij := congrFun (congrFun hX i) j
          have hji := congrFun (congrFun hX j) i
          simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij hji
          simp only [M, Matrix.of_apply]
          split_ifs with h1 h3
          · rfl
          · rw [hij, neg_neg]
          · have he : i = j := le_antisymm (not_lt.mp h3) (not_lt.mp h1)
            subst he
            have h22 : 2 * ((X : Matrix (Fin n) (Fin n) K) * S) i i = 0 := by
              linear_combination hij
            exact ((mul_eq_zero.mp h22).resolve_left h2).symm
        rw [hM, Matrix.mul_assoc, hST, Matrix.mul_one]
      right_inv := by
        intro f
        funext p
        obtain ⟨⟨i, j⟩, h⟩ := p
        show (M f * T * S) i j = f ⟨(i, j), h⟩
        rw [Matrix.mul_assoc, hTS, Matrix.mul_one]
        simp [M, h] }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]

theorem UpperTheory.V.Fr.pr_cfix :
    ∀ (K : Type) [Field K] (n : ℕ) (x : GG (m := n) (R := K)),
      (2 : K) ≠ 0 → x * x = 1 → x.right = -1 →
        2 * Module.finrank K (LinearMap.ker (GG.ad (m := n) (R := K) x - 1)) + n = n * n := by
  intro K _ n x h2 hx hr
  have hg : x.left * theta x.left = 1 := by
    have h := congrArg SemidirectProduct.left hx
    simpa [SemidirectProduct.mul_left, hr, sgnAct_neg_one] using h
  have hG : (x.left : Matrix (Fin n) (Fin n) K)
      = Jmat (R := K) n * (x.left : Matrix (Fin n) (Fin n) K)ᵀ * Jmat (R := K) n := by
    rw [← theta_inv_val, inv_eq_of_mul_eq_one_left hg]
  have hGJ : (x.left : Matrix (Fin n) (Fin n) K) * Jmat (R := K) n
      = Jmat (R := K) n * (x.left : Matrix (Fin n) (Fin n) K)ᵀ := by
    nth_rewrite 1 [hG]
    rw [Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]
  have hST : ((x.left : Matrix (Fin n) (Fin n) K) * Jmat (R := K) n)
      * (Jmat (R := K) n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Jmat (R := K) n), Jmat_mul_Jmat, Matrix.one_mul,
      Units.mul_inv]
  have hTS : (Jmat (R := K) n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat (R := K) n) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      Units.inv_mul, Matrix.one_mul, Jmat_mul_Jmat]
  have hne : x.right ≠ 1 := by
    rw [hr]; decide
  have key : ∀ X : Matrix (Fin n) (Fin n) K,
      X ∈ LinearMap.ker (GG.ad (m := n) (R := K) x - 1) ↔
      (X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat (R := K) n))ᵀ
        = -(X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat (R := K) n)) := by
    intro X
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, GG.ad_apply]
    simp only [one_apply_eq_self, GG.adFun, GG.mat, ite_eq_right hne, thetaLie]
    have hL : (x.left : Matrix (Fin n) (Fin n) K) * -(Jmat (R := K) n * Xᵀ * Jmat (R := K) n)
        * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat (R := K) n)
        = -(X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat (R := K) n))ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Jmat_transpose, ← hGJ]
      simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
      rw [← Matrix.mul_assoc ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        Units.inv_mul, Matrix.one_mul, Jmat_mul_Jmat, Matrix.mul_one]
    constructor
    · intro h
      rw [h] at hL
      nth_rewrite 2 [hL]
      rw [neg_neg]
    · intro h
      rw [h, neg_neg] at hL
      have h' := congrArg (· * (Jmat (R := K) n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) hL
      rw [Matrix.mul_assoc _ ((x.left : Matrix (Fin n) (Fin n) K) * Jmat (R := K) n), hST, Matrix.mul_one,
        Matrix.mul_assoc X, hST, Matrix.mul_one] at h'
      exact h'
  rw [finrank_skew h2 _ _ _ hST hTS key]
  exact card_pairs n
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCount
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_count :
    ∀ {K G W V T : Type} [Field K] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module K W] [Module.Finite K W] [AddCommGroup T] [Module K T] [Module.Finite K T] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G) (ρ : Representation K G W) (b : V → Submodule K W) (φ : T →ₗ[K] (G → W)), (∀ v Y, (∀ s, ρ (loc v s) Y - Y ∈ b v) → Y ∈ b v) → (∀ x ∈ Z1C loc ρ b, ∃ D X, ∀ s, φ D s = x.1 s + (ρ s X - X)) → Module.finrank K (H1C loc ρ b) ≤ Module.finrank K T ∧ ∀ (X₀ : W) (D₀ : T), X₀ ≠ 0 → (∀ s, φ D₀ s = ρ s X₀ - X₀) → Module.finrank K (H1C loc ρ b) + 1 ≤ Module.finrank K T + Module.finrank K (coneH0 ρ b) := by
  intro K G W V T _ _ _ _ _ _ _ _ _ Gv _ loc ρ b φ hA hB
  let cob : W →ₗ[K] (G → W) := LinearMap.pi (fun s => ρ s - LinearMap.id)
  have hcob : ∀ X s, cob X s = ρ s X - X := fun X s => rfl
  let C := LinearMap.range cob
  let f : T →ₗ[K] (G → W) ⧸ C := C.mkQ ∘ₗ φ
  let Ψ : Z1C loc ρ b →ₗ[K] (G → W) ⧸ C :=
    C.mkQ ∘ₗ (LinearMap.fst K (G → W) (V → W)) ∘ₗ (Z1C loc ρ b).subtype
  have hle : Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) ≤ LinearMap.ker Ψ := by
    rintro ⟨x, hx⟩ hxB
    rw [Submodule.mem_comap] at hxB
    obtain ⟨X, hX, -⟩ := hxB
    rw [LinearMap.mem_ker]
    show C.mkQ x.1 = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨X, funext fun s => ((hX s).trans (hcob X s).symm).symm⟩
  have hker : LinearMap.ker Ψ ≤ Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) := by
    rintro ⟨x, hx⟩ hk
    rw [LinearMap.mem_ker] at hk
    change C.mkQ x.1 = 0 at hk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk
    obtain ⟨X, hX⟩ := hk
    obtain ⟨-, -, hloc⟩ := hx
    rw [Submodule.mem_comap]
    refine ⟨X, fun s => (congrFun hX s).symm, fun v => ?_⟩
    have hmem : X - x.2 v ∈ b v := by
      refine hA v _ (fun s => ?_)
      have h1 := hloc v s
      convert h1 using 1
      rw [← hX, hcob, map_sub]
      abel
    have h2 := (b v).neg_mem hmem
    rwa [neg_sub] at h2
  let L := (Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b)).liftQ Ψ hle
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  have hrange : ∀ y, L y ∈ LinearMap.range f := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨D, X, hD⟩ := hB z.1 z.2
    refine ⟨D, ?_⟩
    show C.mkQ (φ D) = C.mkQ z.1.1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨X, funext fun s => ?_⟩
    show cob X s = φ D s - z.1.1 s
    rw [hcob, hD]
    abel
  let L' : H1C loc ρ b →ₗ[K] LinearMap.range f := L.codRestrict _ hrange
  have hinj' : Function.Injective L' := fun a c h => hinj (congrArg Subtype.val h)
  have h1 : Module.finrank K (H1C loc ρ b) ≤ Module.finrank K (LinearMap.range f) :=
    LinearMap.finrank_le_finrank_of_injective hinj'
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := LinearMap.finrank_range_le f
  refine ⟨h1.trans h3, ?_⟩
  intro X₀ D₀ hX₀ hD₀
  by_cases hinv : ∀ s, ρ s X₀ = X₀
  · have hH0 : X₀ ∈ coneH0 ρ b := by
      show (∀ g, ρ g X₀ = X₀) ∧ ∀ v, X₀ ∈ b v
      exact ⟨hinv, fun v => hA v X₀ (fun s => by rw [hinv, sub_self]; exact (b v).zero_mem)⟩
    have h4 : Module.finrank K (coneH0 ρ b) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hH0
      exact hX₀ ((Submodule.mem_bot K).1 hH0)
    omega
  · push_neg at hinv
    obtain ⟨s, hs⟩ := hinv
    have hD0 : D₀ ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      show C.mkQ (φ D₀) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨X₀, funext fun t => (hcob X₀ t).trans (hD₀ t).symm⟩
    have hne : D₀ ≠ 0 := by
      rintro rfl
      apply hs
      have h5 := hD₀ s
      rw [map_zero, Pi.zero_apply] at h5
      exact (sub_eq_zero.1 h5.symm)
    have h4 : Module.finrank K (LinearMap.ker f) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hD0
      exact hne ((Submodule.mem_bot K).1 hD0)
    omega
end

