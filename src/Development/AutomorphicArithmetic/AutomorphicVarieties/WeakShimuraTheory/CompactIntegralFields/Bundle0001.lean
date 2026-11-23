module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AffSmulOne
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section

variable {R : Type} [CommRing R]

private noncomputable def aff (x y : M4 R) : M4 R[X] := Matrix.of fun i j => (1 - X) * C (x i j) + X * C (y i j)

private theorem aff_apply (x y : M4 R) (i j : Fin 4) : aff x y i j = (1 - X) * C (x i j) + X * C (y i j) := rfl

private theorem aff_eq {x y : M4 R} {i j : Fin 4} {c : R} (hx : x i j = c) (hy : y i j = c) : aff x y i j = C c := by
  rw [aff_apply, hx, hy]; ring

private theorem aff_zero {x y : M4 R} {i j : Fin 4} (hx : x i j = 0) (hy : y i j = 0) : aff x y i j = 0 := by
  rw [aff_apply, hx, hy]
  simp

private theorem aff_smul_one (c : R) : aff (c • (1 : M4 R)) (c • 1) = (C c : R[X]) • (1 : M4 R[X]) := by
  refine Matrix.ext fun i j => ?_
  rw [aff_apply]
  by_cases h : i = j
  · subst h
    simp
    ring
  · simp [h]

private theorem aff_one : aff (1 : M4 R) 1 = 1 := by
  ext i j
  rw [aff_apply]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

private theorem adj_aff (x y : M4 R) : adj (aff x y) = aff (adj x) (adj y) := by
  ext i j
  rw [adj_apply, aff_apply, aff_apply, adj_apply, adj_apply, map_zsmul, map_zsmul, smul_add,
    mul_smul_comm, mul_smul_comm]

private structure Cong (x y : M4 R) : Prop where
  x01 : x 0 1 = 0
  x03 : x 0 3 = 0
  x21 : x 2 1 = 0
  x23 : x 2 3 = 0
  y01 : y 0 1 = 0
  y03 : y 0 3 = 0
  y21 : y 2 1 = 0
  y23 : y 2 3 = 0
  e00 : x 0 0 = y 0 0
  e02 : x 0 2 = y 0 2
  e20 : x 2 0 = y 2 0
  e22 : x 2 2 = y 2 2
  e11 : x 1 1 = y 1 1
  e13 : x 1 3 = y 1 3
  e31 : x 3 1 = y 3 1
  e33 : x 3 3 = y 3 3

private theorem Cong.adj {x y : M4 R} (h : Cong x y) : Cong (adj x) (adj y) := by
  have r0 : (0 : Fin 4).rev = 3 := rfl
  have r1 : (1 : Fin 4).rev = 2 := rfl
  have r2 : (2 : Fin 4).rev = 1 := rfl
  have r3 : (3 : Fin 4).rev = 0 := rfl
  constructor <;> simp only [adj_apply, r0, r1, r2, r3, h.x01, h.x03, h.x21, h.x23, h.y01, h.y03,
    h.y21, h.y23, h.e00, h.e02, h.e20, h.e22, h.e11, h.e13, h.e31, h.e33, smul_zero]

private theorem Cong.mul {x y z w : M4 R} (h : Cong x y) (h' : Cong z w) : Cong (x * z) (y * w) := by
  constructor <;> simp only [Matrix.mul_apply, Fin.sum_univ_four, h.x01, h.x03, h.x21, h.x23, h.y01,
    h.y03, h.y21, h.y23, h.e00, h.e02, h.e20, h.e22, h.e11, h.e13, h.e31, h.e33, h'.x01, h'.x03,
    h'.x21, h'.x23, h'.y01, h'.y03, h'.y21, h'.y23, h'.e00, h'.e02, h'.e20, h'.e22, h'.e11, h'.e13,
    h'.e31, h'.e33, mul_zero, zero_mul, add_zero, zero_add]

private theorem Cong.aff_mul {x y z w : M4 R} (h : Cong x y) (h' : Cong z w) :
    aff x y * aff z w = aff (x * z) (y * w) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8⟩ := h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, d1, d2, d3, d4, d5, d6, d7, d8⟩ := h'
  refine Matrix.ext fun i j => ?_
  simp only [aff_apply, Matrix.mul_apply, Fin.sum_univ_four, map_add (f := _), map_mul]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, map_zero, *] <;> ring

private theorem entries_zero_and_relation_of_suppM_of_isGSp {x : M4 R} {ν : R} (hx : SuppM nP x) (gx : IsGSp ν x) :
    x 0 1 = 0 ∧ x 0 2 = 0 ∧ x 0 3 = 0 ∧ x 1 3 = 0 ∧ x 2 1 = 0 ∧ x 2 3 = 0 ∧
      x 0 0 * x 3 1 = x 1 1 * x 2 0 := by
  have r0 : (0 : Fin 4).rev = 3 := rfl
  have r1 : (1 : Fin 4).rev = 2 := rfl
  have r2 : (2 : Fin 4).rev = 1 := rfl
  have r3 : (3 : Fin 4).rev = 0 := rfl
  have s0 : sgn 0 = 1 := rfl
  have s1 : sgn 1 = 1 := rfl
  have s2 : sgn 2 = -1 := rfl
  have s3 : sgn 3 = -1 := rfl
  have a01 : x 0 1 = 0 := hx 0 1 (by decide) (by decide)
  have a02 : x 0 2 = 0 := hx 0 2 (by decide) (by decide)
  have a03 : x 0 3 = 0 := hx 0 3 (by decide) (by decide)
  have a13 : x 1 3 = 0 := hx 1 3 (by decide) (by decide)
  have a21 : x 2 1 = 0 := hx 2 1 (by decide) (by decide)
  have a23 : x 2 3 = 0 := hx 2 3 (by decide) (by decide)
  have ex := congrArg (fun m : M4 R => m 2 0) gx
  simp [IsGSp, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, r0, r1, r2, r3, s0, s1, s2, s3,
    a01, a02, a03, a13, a21, a23] at ex
  refine ⟨a01, a02, a03, a13, a21, a23, ?_⟩
  linear_combination -ex

private theorem cong_of {x y : M4 R} {ν ν' : R} (hx : SuppM nP x) (hy : SuppM nP y) (gx : IsGSp ν x) (gy : IsGSp ν' y)
    (hd : ∀ i, x i i = y i i) (hu : IsUnit (x 0 0)) (h20 : x 2 0 = y 2 0) : Cong x y := by
  obtain ⟨a01, a02, a03, a13, a21, a23, ax⟩ := entries_zero_and_relation_of_suppM_of_isGSp hx gx
  obtain ⟨b01, b02, b03, b13, b21, b23, bx⟩ := entries_zero_and_relation_of_suppM_of_isGSp hy gy
  refine ⟨a01, a03, a21, a23, b01, b03, b21, b23, hd 0, a02.trans b02.symm, h20, hd 2, hd 1,
    a13.trans b13.symm, ?_, hd 3⟩
  refine hu.mul_left_cancel ?_
  rw [ax, hd 0, bx, hd 1, h20]

private theorem supp_nP {x : M4 R} (h : SuppM qQ x) : SuppM nP x := by
  intro i j hij hw
  refine h i j hij fun hq => hw ?_
  simp only [qQ, nP, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  tauto

private theorem lc_of_cont {Γ : Type} [TopologicalSpace Γ] {f : Γ → R} (h : AdicCont ⊥ f) : IsLocallyConstant f := by
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]

end

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.lineP :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ c c' : PD Φ.ι Γ k, Φ.IsRes a c → Φ.IsRes a c' → c.In nP → c'.In nP → c.SamePs c' → Φ.Linked a c c' := by
  intro O Γ _ _ _ _ _ _ Φ k _ a hΦ c c' hc hc' hin hin' hs
  have cong : ∀ g, Cong (c.r g) (c'.r g) := fun g =>
    cong_of (hin.1 g) (hin'.1 g) (hc.pair.mult g) (hc'.pair.mult g)
      (fun i => (hc.res.diag g i).trans (hc'.res.diag g i).symm)
      (by rw [hc.res.diag g 0]; exact (Φ.χ 0 g).isUnit.map a) (hs.1 g)
  have congN : ∀ v, Cong (c.n v) (c'.n v) := fun v =>
    cong_of (supp_nP (hin.2 v)) (supp_nP (hin'.2 v)) (hc.pair.low v).1 (hc'.pair.low v).1
      (fun i => ((hc.pair.low v).2.1 i).trans ((hc'.pair.low v).2.1 i).symm)
      (by rw [(hc.pair.low v).2.1 0]; exact isUnit_one) (hs.2 v)
  have gsp : ∀ {x y : M4 k} {ν : k}, Cong x y → IsGSp ν x → IsGSp ν y → IsGSp (C ν) (aff x y) := by
    intro x y ν h gx gy
    unfold IsGSp at *
    rw [adj_aff, h.adj.aff_mul h, gx, gy, aff_smul_one]
  obtain ⟨ρ, hr⟩ : ∃ ρ : Γ →* M4 k[X], ∀ g, ρ g = aff (c.r g) (c'.r g) :=
    ⟨{ toFun := fun g => aff (c.r g) (c'.r g)
       map_one' := by
         show aff (c.r 1) (c'.r 1) = 1
         rw [map_one, map_one, aff_one]
       map_mul' := fun g h => by
         show aff (c.r (g * h)) (c'.r (g * h)) = aff (c.r g) (c'.r g) * aff (c.r h) (c'.r h)
         rw [map_mul, map_mul, (cong g).aff_mul (cong h)] }, fun _ => rfl⟩
  have conj : ∀ v s, adj (aff (c.n v) (c'.n v)) * ρ s * aff (c.n v) (c'.n v) =
      aff (adj (c.n v) * c.r s * c.n v) (adj (c'.n v) * c'.r s * c'.n v) := by
    intro v s
    rw [hr, adj_aff, (congN v).adj.aff_mul (cong s), ((congN v).adj.mul (cong s)).aff_mul (congN v)]
  refine ⟨⟨ρ, fun v => aff (c.n v) (c'.n v)⟩, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro g
    dsimp only
    rw [hr]
    exact gsp (cong g) (hc.pair.mult g) (hc'.pair.mult g)
  · intro g hg
    dsimp only
    rw [hr, hc.pair.kill g hg, hc'.pair.kill g hg, aff_one]
  · intro i j hij
    dsimp only
    rw [hr]
    exact aff_zero (hc.pair.nrm hij) (hc'.pair.nrm hij)
  · intro v
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · have h1 := gsp (congN v) (hc.pair.low v).1 (hc'.pair.low v).1
      rwa [map_one] at h1
    · exact (aff_eq ((hc.pair.low v).2.1 i) ((hc'.pair.low v).2.1 i)).trans (map_one C)
    · exact aff_zero ((hc.pair.low v).2.2 i j hij) ((hc'.pair.low v).2.2 i j hij)
  · intro v s hs' i j hij
    dsimp only
    rw [conj]
    exact aff_zero (hc.pair.flag v s hs' i j hij) (hc'.pair.flag v s hs' i j hij)
  · intro v s hs' i
    unfold PD.ψ
    dsimp only
    rw [conj]
    exact (aff_eq (hc.pair.mu v s hs' i) (hc'.pair.mu v s hs' i)).trans (map_one C)
  · intro g i
    dsimp only
    rw [hr]
    exact aff_eq (hc.res.diag g i) (hc'.res.diag g i)
  · intro v s hs' i
    unfold PD.ψ
    dsimp only
    rw [conj]
    exact aff_eq (hc.res.char v s hs' i) (hc'.res.char v s hs' i)
  · left
    refine ⟨fun g i j hij hw => ?_, fun v i j hij hw => ?_⟩
    · dsimp only
      rw [hr]
      exact aff_zero (hin.1 g i j hij hw) (hin'.1 g i j hij hw)
    · exact aff_zero (hin.2 v i j hij hw) (hin'.2 v i j hij hw)
  · intro i j N
    have l1 := lc_of_cont (hc.cont i j)
    have l2 := lc_of_cont (hc'.cont i j)
    have l3 := IsLocallyConstant.comp₂ l1 l2
      (fun u w => Ideal.Quotient.mk ((⊥ : Ideal k[X]) ^ N) ((1 - X) * C u + X * C w))
    dsimp only
    simp only [hr, aff_apply]
    exact l3
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, mapRep, hr, aff_apply]
    · funext v
      ext i j
      simp [PD.map, aff_apply]
  · refine PD.ext ?_ ?_
    · ext g i j
      simp [PD.map, mapRep, hr, aff_apply]
    · funext v
      ext i j
      simp [PD.map, aff_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AlgHomResUnique
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem algHom_res_unique {Λ B : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing B] [Algebra Λ B] [IsCO Λ B]
    (f : B →ₐ[Λ] ResidueField Λ) (b : B) : f b = res Λ B b := by
  obtain ⟨c, hc⟩ := IsCO.res_surj (O := Λ) b
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Λ B d, by rw [AlgHom.commutes]; rfl⟩
  have hmax : (RingHom.ker (f : B →+* ResidueField Λ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  have hk : RingHom.ker (f : B →+* ResidueField Λ) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  have h1 : f (b - algebraMap Λ B c) = 0 := by
    have hm : b - algebraMap Λ B c ∈ RingHom.ker (f : B →+* ResidueField Λ) := hk ▸ hc
    simpa using hm
  have h2 : res Λ B (b - algebraMap Λ B c) = 0 := (res_eq_zero_iff Λ B _).2 hc
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, AlgHom.commutes, AlgHom.commutes]

private theorem point_ext {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) (x y : X.A →ₐ[Λ] ResidueField Λ)
    (h : X.P.map (x : X.A →+* ResidueField Λ) = X.P.map (y : X.A →+* ResidueField Λ)) (z : X.A) : x z = y z := by
  have hB : ∀ b : X.B, x (algebraMap X.B X.A b) = y (algebraMap X.B X.A b) := by
    intro b
    have h1 := algHom_res_unique (x.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b
    have h2 := algHom_res_unique (y.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2
    rw [h1, h2]
  have hz : z ∈ (⊤ : Subalgebra X.B X.A) := trivial
  rw [← X.gen] at hz
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    rcases hw with ⟨⟨g, i, j⟩, rfl⟩ | ⟨⟨v, i, j⟩, rfl⟩
    · exact congrArg (fun Q => Q.r g i j) h
    · exact congrArg (fun Q => Q.n v i j) h
  | algebraMap b => exact hB b
  | add u w _ _ hu hw => rw [map_add (f := _), map_add (f := _), hu, hw]
  | mul u w _ _ hu hw => rw [map_mul, map_mul, hu, hw]

private theorem ker_le_of_eval {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type}
    [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) (x : X.A →ₐ[Λ] ResidueField Λ)
    (f : X.A →ₐ[Λ] (ResidueField Λ)[X]) (t : ResidueField Λ)
    (h : (X.P.map (f : X.A →+* (ResidueField Λ)[X])).map (evalRingHom t) = X.P.map (x : X.A →+* ResidueField Λ)) :
    RingHom.ker f ≤ RingHom.ker x := by
  intro z hz
  have hy : X.P.map ((((Polynomial.aeval t).restrictScalars Λ).comp f : X.A →ₐ[Λ] ResidueField Λ) :
      X.A →+* ResidueField Λ) = X.P.map (x : X.A →+* ResidueField Λ) := by
    rw [← h]; rfl
  have hxz := point_ext X _ x hy z
  rw [RingHom.mem_ker] at hz ⊢
  rw [← hxz]
  simp [hz]

theorem UpperTheory.V.Ws.conn :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ (X : Space Φ a) (J : Ideal X.B) (x x' : X.A →ₐ[Λ] ResidueField Λ),
      Φ.Linked ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) (X.P.map (x' : X.A →+* ResidueField Λ)) →
      (X.AllIn J (RingHom.ker x) → X.SomeIn J (RingHom.ker x')) ∧ (X.AllIn J (RingHom.ker x') → X.SomeIn J (RingHom.ker x)) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a _ X J x x' hL
  obtain ⟨Q, hQ, h0, h1⟩ := hL
  obtain ⟨f, hf, -⟩ := X.line Q hQ
  have k0 : RingHom.ker f ≤ RingHom.ker x := ker_le_of_eval X x f 0 (by rw [hf, h0])
  have k1 : RingHom.ker f ≤ RingHom.ker x' := ker_le_of_eval X x' f 1 (by rw [hf, h1])
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  obtain ⟨q, hq, hqf⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker f) bot_le
  exact ⟨fun hA => ⟨q, hq, hqf.trans k1, hA q hq (hqf.trans k0)⟩,
    fun hA => ⟨q, hq, hqf.trans k0, hA q hq (hqf.trans k1)⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.BlockDet
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private theorem bd_up_mul {Y Z : M4 R} (hY : IsUp Y) (hZ : IsUp Z) : IsUp (Y * Z) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : k < i
  · rw [hY i k h, zero_mul]
  · rw [hZ k j (lt_of_lt_of_le hij (not_lt.mp h)), mul_zero]

private theorem bd_up_diag {Y Z : M4 R} (hY : IsUp Y) (hZ : IsUp Z) (i : Fin 4) : (Y * Z) i i = Y i i * Z i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hY i k h, zero_mul]
  · rw [hZ k i h, mul_zero]

private theorem bd_conj_mul {u v : M4 R} (h : u * v = 1) (Y Z : M4 R) :
    v * (Y * Z) * u = (v * Y * u) * (v * Z * u) := by
  have : (v * Y * u) * (v * Z * u) = v * Y * (u * v) * Z * u := by simp only [Matrix.mul_assoc]
  rw [this, h]; simp only [Matrix.mul_assoc, Matrix.one_mul]

private theorem bd_trace {u v : M4 R} (h : u * v = 1) (Y : M4 R) : (v * Y * u).trace = Y.trace := by
  rw [Matrix.trace_mul_cycle, h, Matrix.one_mul]

private theorem bd_key {u v N X : M4 R} (h : u * v = 1) (hN : IsUp (v * N * u)) (hX : IsUp (v * X * u)) :
    (N * X).trace ^ 2 - ((N * X) * (N * X)).trace =
      (∑ i, (v * N * u) i i * (v * X * u) i i) ^ 2 - ∑ i, ((v * N * u) i i * (v * X * u) i i) ^ 2 := by
  have hU := bd_up_mul hN hX
  rw [← bd_trace h (N * X), ← bd_trace h ((N * X) * (N * X)), bd_conj_mul h (N * X), bd_conj_mul h N X]
  simp only [Matrix.trace, Matrix.diag_apply, bd_up_diag hU hU, bd_up_diag hN hX, sq]

private theorem bd_poly {u v S : M4 R} (h : u * v = 1) (h' : v * u = 1) (b c : R) :
    v * (S * S - b • S + c • (1 : M4 R)) * u = (v * S * u) * (v * S * u) - b • (v * S * u) + c • (1 : M4 R) := by
  rw [← bd_conj_mul h]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h']

private theorem bd_poly_up {T : M4 R} (hT : IsUp T) (b c : R) : IsUp (T * T - b • T + c • (1 : M4 R)) := by
  intro i j hij
  simp [bd_up_mul hT hT i j hij, hT i j hij, Matrix.one_apply_ne hij.ne']

private theorem bd_poly_diag {T : M4 R} (hT : IsUp T) (b c : R) (i : Fin 4) :
    (T * T - b • T + c • (1 : M4 R)) i i = T i i * T i i - b * T i i + c := by
  simp [bd_up_diag hT hT]

private theorem bd_notMem (m : Ideal R) [hm : m.IsPrime] {t x p q p' q' r s : R} (ht : t - x ∈ m) (hp : p' - p ∈ m)
    (hq : q' - q ∈ m) (hr : r ∈ m) (h1 : x - p ∉ m) (h2 : x - q ∉ m) :
    t * t - (p' + q') * t + (p' * q' - r * s) ≠ 0 := by
  intro h0
  have e : (x - p) * (x - q) ∈ m := by
    rw [← Ideal.Quotient.eq] at ht hp hq
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hr ⊢
    have := congrArg (Ideal.Quotient.mk m) h0
    simp only [map_add (f := _), map_sub, map_mul, map_zero, ht, hp, hq, hr] at this ⊢
    linear_combination this
  rcases hm.mem_or_mem e with e | e
  · exact h1 e
  · exact h2 e

private theorem bd_zero {S : M4 R} (h : IsBlock S) : S 0 1 = 0 ∧ S 0 3 = 0 ∧ S 1 0 = 0 ∧ S 1 2 = 0 ∧ S 2 1 = 0 ∧
    S 2 3 = 0 ∧ S 3 0 = 0 ∧ S 3 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact h _ _ (by decide)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.blockDet :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (m : Ideal R) [m.IsPrime] (a : Fin 4 → R) (u v S X : M4 R), v * u = 1 →
          (∀ i j, lamW i ≠ lamW j → a i - a j ∉ m) → IsBlock S → (∀ i j, S i j - Matrix.diagonal a i j ∈ m) → IsUp (v * S * u) →
          (∀ i, (v * S * u) i i - a i ∈ m) → IsBlock X → IsUp (v * X * u) →
          (X.submatrix ixA ixA).det = (v * X * u) 0 0 * (v * X * u) 2 2 ∧ (X.submatrix ixB ixB).det = (v * X * u) 1 1 * (v * X * u) 3 3 := by
  intro R _ _ _ m _ a u v S X hvu ha hS hSa hT hTa hX hY
  have huv : u * v = 1 := mul_eq_one_comm.mp hvu
  obtain ⟨s01, s03, s10, s12, s21, s23, s30, s32⟩ := bd_zero hS
  obtain ⟨x01, x03, x10, x12, x21, x23, x30, x32⟩ := bd_zero hX
  have hd : ∀ i, S i i - a i ∈ m := fun i => by simpa using hSa i i
  have h13 : S 1 3 ∈ m := by simpa using hSa 1 3
  have h02 : S 0 2 ∈ m := by simpa using hSa 0 2
  obtain ⟨N, hN⟩ : ∃ N, N = S * S - (S 1 1 + S 3 3) • S + (S 1 1 * S 3 3 - S 1 3 * S 3 1) • (1 : M4 R) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ N, N = S * S - (S 0 0 + S 2 2) • S + (S 0 0 * S 2 2 - S 0 2 * S 2 0) • (1 : M4 R) := ⟨_, rfl⟩
  have hNz : ∀ i j, (lamW i = 0 ∨ lamW j = 0) → N i j = 0 := by
    intro i j h
    subst hN
    fin_cases i <;> fin_cases j <;> first | (exact absurd h (by decide)) |
      (simp [Matrix.mul_apply, Fin.sum_univ_four, s01, s03, s10, s12, s21, s23, s30, s32]; try ring)
  have hMz : ∀ i j, (lamW i = 1 ∨ lamW j = 1) → M i j = 0 := by
    intro i j h
    subst hM
    fin_cases i <;> fin_cases j <;> first | (exact absurd h (by decide)) |
      (simp [Matrix.mul_apply, Fin.sum_univ_four, s01, s03, s10, s12, s21, s23, s30, s32]; try ring)
  have hNM : N * M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_four, hMz 0 j (Or.inl rfl), hMz 2 j (Or.inl rfl), hNz i 1 (Or.inr rfl),
      hNz i 3 (Or.inr rfl)]
    simp
  have uN : IsUp (v * N * u) := by rw [hN, bd_poly huv hvu]; exact bd_poly_up hT _ _
  have uM : IsUp (v * M * u) := by rw [hM, bd_poly huv hvu]; exact bd_poly_up hT _ _
  have nN : ∀ i, lamW i = 1 → (v * N * u) i i ≠ 0 := by
    intro i hi
    rw [hN, bd_poly huv hvu, bd_poly_diag hT]
    exact bd_notMem m (hTa i) (hd 1) (hd 3) h13 (ha i 1 (by rw [hi]; decide)) (ha i 3 (by rw [hi]; decide))
  have nM : ∀ i, lamW i = 0 → (v * M * u) i i ≠ 0 := by
    intro i hi
    rw [hM, bd_poly huv hvu, bd_poly_diag hT]
    exact bd_notMem m (hTa i) (hd 0) (hd 2) h02 (ha i 0 (by rw [hi]; decide)) (ha i 2 (by rw [hi]; decide))
  have hz : ∀ i, (v * N * u) i i * (v * M * u) i i = 0 := by
    intro i
    rw [← bd_up_diag uN uM, ← bd_conj_mul huv, hNM]; simp
  have n1 : (v * N * u) 1 1 = 0 := (mul_eq_zero.mp (hz 1)).resolve_right (nM 1 rfl)
  have n3 : (v * N * u) 3 3 = 0 := (mul_eq_zero.mp (hz 3)).resolve_right (nM 3 rfl)
  have m0 : (v * M * u) 0 0 = 0 := (mul_eq_zero.mp (hz 0)).resolve_left (nN 0 rfl)
  have m2 : (v * M * u) 2 2 = 0 := (mul_eq_zero.mp (hz 2)).resolve_left (nN 2 rfl)
  have u1 : IsUp (v * 1 * u) := by
    rw [Matrix.mul_one, hvu]; intro i j hij; exact Matrix.one_apply_ne hij.ne'
  have two : (2 : R) ≠ 0 := two_ne_zero
  constructor
  · have k1 := bd_key huv uN u1
    have k2 := bd_key huv uN hY
    have z1 : ∀ i, N i 1 = 0 := fun i => hNz i 1 (Or.inr rfl)
    have z3 : ∀ i, N i 3 = 0 := fun i => hNz i 3 (Or.inr rfl)
    have z1' : ∀ i, N 1 i = 0 := fun i => hNz 1 i (Or.inl rfl)
    have z3' : ∀ i, N 3 i = 0 := fun i => hNz 3 i (Or.inl rfl)
    have p0 := nN 0 rfl
    have p2 := nN 2 rfl
    rw [Matrix.mul_one v, hvu] at k1
    generalize v * N * u = N' at *
    generalize v * X * u = X' at *
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mul_one,
      Matrix.one_apply_eq, z1, z3, z1', z3', n1, n3, x01, x03, x10, x12, x21, x23, x30, x32] at k1 k2
    apply mul_left_cancel₀ (mul_ne_zero two (mul_ne_zero p0 p2))
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, ixA, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination k2 - (X 0 0 * X 2 2 - X 0 2 * X 2 0) * k1
  · have k1 := bd_key huv uM u1
    have k2 := bd_key huv uM hY
    have z1 : ∀ i, M i 0 = 0 := fun i => hMz i 0 (Or.inr rfl)
    have z3 : ∀ i, M i 2 = 0 := fun i => hMz i 2 (Or.inr rfl)
    have z1' : ∀ i, M 0 i = 0 := fun i => hMz 0 i (Or.inl rfl)
    have z3' : ∀ i, M 2 i = 0 := fun i => hMz 2 i (Or.inl rfl)
    have p0 := nM 1 rfl
    have p2 := nM 3 rfl
    rw [Matrix.mul_one v, hvu] at k1
    generalize v * M * u = N' at *
    generalize v * X * u = X' at *
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mul_one,
      Matrix.one_apply_eq, z1, z3, z1', z3', m0, m2, x01, x03, x10, x12, x21, x23, x30, x32] at k1 k2
    apply mul_left_cancel₀ (mul_ne_zero two (mul_ne_zero p0 p2))
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply, ixB, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination k2 - (X 1 1 * X 3 3 - X 1 3 * X 3 1) * k1
end

