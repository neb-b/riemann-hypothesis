module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0050

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AbelianFieldWindowTripleSnoc
section
open Module in
theorem UpperTheory.abelianField_window_triple_snoc :
    UpperTheory.V.Af.Wd.TriSnoc := by
  unfold UpperTheory.V.Af.Wd.TriSnoc
  intro k W' W W'' ι _ _ _ _ _ _ _ n T' T T'' f p hf hp hex h1 hT' hT'' d hd hd''
  unfold UpperTheory.V.Af.Wd.IsTri at hd ⊢
  obtain ⟨b', hb'⟩ := hd
  obtain ⟨y, hy0, hyspan⟩ := (finrank_eq_one_iff').1 h1
  obtain ⟨s, hs⟩ := hp y
  have hrange : Submodule.span k (Set.range fun i => f (b' i)) ≤ LinearMap.ker p := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (hex _).2 ⟨_, rfl⟩
  have hli : LinearIndependent k (Fin.snoc (fun i => f (b' i)) s : Fin (n + 1) → W) := by
    rw [linearIndependent_finSnoc]
    refine ⟨b'.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
    intro hmem
    have h0 : p s = 0 := LinearMap.mem_ker.1 (hrange hmem)
    rw [hs] at h0
    exact hy0 h0
  have hsp : ⊤ ≤ Submodule.span k (Set.range (Fin.snoc (fun i => f (b' i)) s : Fin (n + 1) → W)) := by
    intro w _
    obtain ⟨c, hc⟩ := hyspan (p w)
    have hker : p (w - c • s) = 0 := by rw [map_sub, map_smul, hs, hc, sub_self]
    obtain ⟨x, hx⟩ := (hex _).1 hker
    have hw : w = f x + c • s := by rw [hx]; abel
    rw [hw]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last n, by simp⟩))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b'.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, by simp⟩)
  set b := Module.Basis.mk hli hsp with hbdef
  have hbc : ∀ i, b i.castSucc = f (b' i) := fun i => by simp [b]
  have hbl : b (Fin.last n) = s := by simp [b]
  have hfx : ∀ x : W', f x = ∑ i, (b'.repr x i) • b i.castSucc := by
    intro x
    conv_lhs => rw [← b'.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, hbc]
  have hrepr1 : ∀ (x : W') (i : Fin n), b.repr (f x) i.castSucc = b'.repr x i := by
    intro x i
    rw [hfx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finsupp.single_apply, Fin.castSucc_inj]
  have hrepr2 : ∀ x : W', b.repr (f x) (Fin.last n) = 0 := by
    intro x
    rw [hfx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  refine ⟨b, fun a => ⟨?_, ?_⟩⟩
  · intro i j hji
    rw [LinearMap.toMatrix_apply]
    induction j using Fin.lastCases with
    | last => exact absurd hji (not_lt.2 (Fin.le_last i))
    | cast j =>
      rw [hbc, ← hT']
      induction i using Fin.lastCases with
      | last => exact hrepr2 _
      | cast i =>
        rw [hrepr1]
        have := (hb' a).1 i j (Fin.castSucc_lt_castSucc_iff.1 hji)
        rwa [LinearMap.toMatrix_apply] at this
  · intro i
    rw [LinearMap.toMatrix_apply]
    induction i using Fin.lastCases with
    | last =>
      rw [hbl]
      have hker : p (T a s - d a (Fin.last n) • s) = 0 := by
        rw [map_sub, map_smul, hT'', hs, hd'', sub_self]
      obtain ⟨x, hx⟩ := (hex _).1 hker
      have hTs : T a s = f x + d a (Fin.last n) • s := by rw [hx]; abel
      rw [hTs, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, hrepr2, ← hbl, b.repr_self]
      simp
    | cast i =>
      rw [hbc, ← hT', hrepr1]
      have := (hb' a).2 i
      rwa [LinearMap.toMatrix_apply] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicBaseChangeRealPart
section
open NumberField Matrix UpperTheory.V.KT UpperTheory.V.Af.BA ComplexOrder in
theorem UpperTheory.adelicBaseChange_realPart :
    UpperTheory.V.Af.BA.RePart := by
  intro L _ _ N σ hσ k
  let A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ :=
    fun w => Matrix.of fun i j => (((mat k w) i j).re : ℂ)
  have hre : ∀ w i j, ((mat k w) j i).re = ((mat k w) i j).re := by
    intro w i j
    have := (mat_herm k w).apply i j
    rw [← this]
    simp
  have hA : ∀ w, (A w).IsHermitian := by
    intro w
    ext i j
    simp [A, Matrix.conjTranspose_apply, hre w i j]
  have hmat : ∀ w, mat (mkHS A hA) w = A w := fun w => rfl
  have hAeq : ∀ w, A w = (1 / 2 : ℝ) • (mat k w + (mat k w).transpose) := by
    intro w
    ext i j
    have h1 := (mat_herm k w).apply i j
    have h2 : (mat k w) j i = star ((mat k w) i j) := by rw [← h1, star_star]
    simp only [A, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, h2]
    apply Complex.ext <;> simp <;> ring
  refine ⟨⟨mkHS A hA, ?_⟩, ?_, ?_⟩
  · intro w i j
    show ((mat (mkHS A hA) w) i j).im = 0
    rw [hmat]
    simp [A]
  · intro y
    show q (mkHS A hA) y = _
    have hz : ∀ w i, toR (sLat σ y) w i = star (toR y w i) := fun w i => hσ w (y i)
    simp only [q, qR]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hmat]
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum,
      ← Finset.sum_add_distrib, Finset.sum_div, hz]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [A, Matrix.of_apply, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · intro hk
    have hpsd : ∀ w, (A w).PosSemidef := by
      intro w
      rw [hAeq w]
      exact ((hk w).add (hk w).transpose).smul (by norm_num)
    refine ⟨fun w => by rw [hmat]; exact hpsd w, fun h0 => ?_⟩
    apply HS_ext
    intro w
    have hA0 : A w = 0 := by
      have := congrArg (fun x : HR L N => mat (x : HS L N) w) h0
      simpa [hmat, mat_zero] using this
    rw [mat_zero]
    apply ((hk w).trace_eq_zero_iff).mp
    have hd : ∀ i, (mat k w) i i = (((mat k w) i i).re : ℂ) := by
      intro i
      apply Complex.ext
      · simp
      · have := (mat_herm k w).apply i i
        have h3 := congrArg Complex.im this
        simp at h3
        simp
        linarith
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.diag_apply, hd i]
    have := congrFun (congrFun hA0 i) i
    simpa [A] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRealPartInvariant
section
open NumberField Matrix UpperTheory.V.KT UpperTheory.V.Af.BA in
theorem UpperTheory.adelic_realPart_invariant :
    UpperTheory.V.Af.BA.ReInv := by
  intro L _ _ N σ hσ
  refine ⟨fun x => ?_, fun h hh => ⟨fun y => ?_, fun g hg => ?_⟩⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
    have e : embO w (σ (σ x)) = embO w x := by rw [hσ, hσ]; simp
    apply RingOfIntegers.coe_injective
    exact w.embedding.injective (by simpa [embO] using e)
  · have hz : ∀ w i, toR (sLat σ y) w i = star (toR y w i) := fun w i => hσ w (y i)
    simp only [q, qR]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, hz]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have him : ((mat h w) i j).im = 0 := hh w i j
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, him]
    ring
  · have hfix : ∀ i j, σ ((↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j)
        = (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j := fun i j => by
      have := congrArg (fun u : Gm L N => (u : Matrix (Fin N) (Fin N) (𝓞 L)) i j)
        (mem_Fix.mp (inv_mem hg))
      exact this
    intro w i j
    have hs : g • h = pull (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) h := rfl
    show ((mat (g • h) w) i j).im = 0
    rw [hs, mat_pull]
    set B := (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hBdef
    have hB : B.map (starRingEnd ℂ) = B := by
      ext a b
      simp only [hBdef, Matrix.map_apply]
      rw [← hσ w, hfix]
    have hM : (mat h w).map (starRingEnd ℂ) = mat h w := by
      ext a b
      simp only [Matrix.map_apply]
      exact Complex.conj_eq_iff_im.mpr (hh w a b)
    have hBt : Bᴴ.map (starRingEnd ℂ) = Bᴴ := by
      ext a b
      have := congrFun (congrFun hB b) a
      simp only [Matrix.map_apply, Matrix.conjTranspose_apply] at this ⊢
      simp only [Complex.star_def, Complex.conj_conj]
      exact this.symm
    have hP : (Bᴴ * mat h w * B).map (starRingEnd ℂ) = Bᴴ * mat h w * B := by
      rw [Matrix.map_mul, Matrix.map_mul, hBt, hM, hB]
    have := congrFun (congrFun hP i) j
    simp only [Matrix.map_apply] at this
    exact Complex.conj_eq_iff_im.mp this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedCommOfBoundedEquiv
section
theorem UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv → UpperTheory.V.Af.BA.BddSub → UpperTheory.V.Af.BA.BddOver → UpperTheory.V.Af.BA.BddComm := by
  intro hEq hSub hOver G _ Γ Λ hc hΛ
  obtain ⟨h1, h2⟩ := hc
  have f1 : (Γ.subgroupOf Λ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h1
  have f2 : (Λ.subgroupOf Γ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h2
  have b1 := hSub Λ (Γ.subgroupOf Λ) f1 hΛ
  have e : (Γ.subgroupOf Λ) ≃* (Λ.subgroupOf Γ) :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have b2 := hEq _ _ ⟨e⟩ b1
  exact hOver Γ (Λ.subgroupOf Γ) f2 b2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOfDegreeBounded
section
private theorem UpperTheory.cardinal_sum_eq_finite_sum_range (N : ℕ) : ∀ f : ℕ → Cardinal.{0}, (∀ q, N ≤ q → f q = 0) →
    Cardinal.sum f = ∑ q ∈ Finset.range N, f q := by
  induction N with
  | zero =>
    intro f hf
    have hf0 : f = fun _ => 0 := funext fun q => hf q (Nat.zero_le q)
    subst hf0
    rw [Cardinal.sum_const', mul_zero, Finset.sum_range_zero]
  | succ N ih =>
    intro f hf
    rw [Cardinal.sum_nat_eq_add_sum_succ, ih (fun i => f (i+1)) (fun q hq => hf (q+1) (by omega)),
      Finset.sum_range_succ', add_comm]

theorem UpperTheory.adelic_rep_bounded_of_degree_bounded :
    UpperTheory.V.Af.BA.BddOfDeg := by
  unfold UpperTheory.V.Af.BA.BddOfDeg
  intro Γ _ hc hD
  choose c hc using hc
  obtain ⟨D, hD⟩ := hD
  unfold UpperTheory.V.Af.CohB.Bdd
  refine ⟨∑ q ∈ Finset.range D, c q, fun A => ?_⟩
  unfold UpperTheory.V.Af.CohB.totCoh
  rw [UpperTheory.cardinal_sum_eq_finite_sum_range D _ (fun q hq => hD q hq A), Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun q _ => hc q A
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOfSubgroupBounded
section
open CategoryTheory UpperTheory.V.Af.CohB in
theorem UpperTheory.adelic_rep_bounded_of_subgroup_bounded :
    UpperTheory.V.Af.BA.BddSub := by
  classical
  unfold UpperTheory.V.Af.BA.BddSub
  intro G _ S hS hB
  haveI := hS
  unfold UpperTheory.V.Af.CohB.Bdd at hB ⊢
  obtain ⟨c, hc⟩ := hB
  haveI : Finite (Quotient (QuotientGroup.rightRel S)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  have hrank : ∀ B : Rep.{0,0,0} ℂ S, Module.rank ℂ ↑(Rep.coind S.subtype B) ≤
      (Nat.card (Quotient (QuotientGroup.rightRel S)) : Cardinal) * Module.rank ℂ ↑B := by
    intro B
    let L : ↥(Representation.coindV S.subtype B.ρ) →ₗ[ℂ]
        (Quotient (QuotientGroup.rightRel S) → ↑B) :=
      { toFun := fun f q => f.1 q.out
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hL : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro f hf
      apply Subtype.ext
      funext g
      show f.1 g = 0
      let o : G := (Quotient.mk (QuotientGroup.rightRel S) g).out
      have h1 : Quotient.mk (QuotientGroup.rightRel S) o = Quotient.mk (QuotientGroup.rightRel S) g :=
        Quotient.out_eq _
      have h2 : g * o⁻¹ ∈ S := QuotientGroup.rightRel_apply.mp (Quotient.exact h1)
      let s : S := ⟨g * o⁻¹, h2⟩
      have hfo : f.1 o = 0 := congrFun hf (Quotient.mk (QuotientGroup.rightRel S) g)
      have hso : S.subtype s * o = g := by
        show g * o⁻¹ * o = g
        rw [inv_mul_cancel_right]
      calc f.1 g = f.1 (S.subtype s * o) := by rw [hso]
        _ = B.ρ s (f.1 o) := f.2 s o
        _ = 0 := by rw [hfo, map_zero]
    calc Module.rank ℂ ↑(Rep.coind S.subtype B)
        = Module.rank ℂ ↥(Representation.coindV S.subtype B.ρ) := rfl
      _ ≤ Module.rank ℂ (Quotient (QuotientGroup.rightRel S) → ↑B) :=
        LinearMap.rank_le_of_injective L hL
      _ = Cardinal.mk (Quotient (QuotientGroup.rightRel S)) * Module.rank ℂ ↑B := by
        rw [rank_pi, Cardinal.sum_const']
      _ = (Nat.card (Quotient (QuotientGroup.rightRel S)) : Cardinal) * Module.rank ℂ ↑B := by
        rw [Nat.cast_card]
  refine ⟨c * Nat.card (Quotient (QuotientGroup.rightRel S)), fun B => ?_⟩
  have htot : UpperTheory.V.Af.CohB.totCoh B = UpperTheory.V.Af.CohB.totCoh (Rep.coind S.subtype B) := by
    unfold UpperTheory.V.Af.CohB.totCoh
    congr 1
    funext q
    exact ((groupCohomology.coindIso B q).toLinearEquiv).rank_eq.symm
  rw [htot, Nat.cast_mul, mul_assoc]
  refine (hc _).trans ?_
  gcongr
  exact hrank B
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOverOfSumBoundCoindRetract
section
open CategoryTheory in
theorem UpperTheory.adelic_rep_bounded_over_of_sum_bound_coind_retract :
    UpperTheory.V.Af.CohB.SumBound → UpperTheory.V.Af.BA.CoindRetract → UpperTheory.V.Af.BA.BddOver := by
  intro hSum hRet
  unfold UpperTheory.V.Af.BA.BddOver
  intro G _ S hS hB
  unfold UpperTheory.V.Af.CohB.Bdd at hB ⊢
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, fun A => ?_⟩
  obtain ⟨π, ι, hπι⟩ := hRet G S hS A
  have hq : ∀ q, Module.rank ℂ ↑(groupCohomology A q) ≤
      Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q) := by
    intro q
    have h1 := hSum G Unit A (fun _ => Rep.coind S.subtype (Rep.res S.subtype A))
      (fun _ => π) (fun _ => ι) (by rw [Fintype.sum_unique]; exact hπι) q
    rw [Fintype.sum_unique,
      ((groupCohomology.coindIso (Rep.res S.subtype A) q).toLinearEquiv).rank_eq] at h1
    exact h1
  calc UpperTheory.V.Af.CohB.totCoh A
      = Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology A q)) := rfl
    _ ≤ Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q)) :=
      Cardinal.sum_le_sum _ _ hq
    _ = UpperTheory.V.Af.CohB.totCoh (Rep.res S.subtype A) := rfl
    _ ≤ c * Module.rank ℂ ↑(Rep.res S.subtype A) := hc _
    _ = c * Module.rank ℂ ↑A := rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepDimensionBounded
section
open UpperTheory.V.Af.BA in
theorem UpperTheory.adelic_rep_dimension_bounded :
    UpperTheory.V.Af.BA.DimBdd := by
  classical
  unfold UpperTheory.V.Af.BA.DimBdd
  intro Γ I _ _ K hfin hstab0
  have hre : ∀ {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) (t : K.Tup q) (g : Γ),
      g • t = t → g • K.re f t = K.re f t := by
    intro p q f t g hg
    show K.re f (g • t) = K.re f t
    rw [hg]
  have hst : ∀ (p : ℕ) (t : K.Tup p), Finite ↥(MulAction.stabilizer Γ t) := by
    intro p t
    haveI := hstab0 (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t)
    have hle : MulAction.stabilizer Γ t ≤
        MulAction.stabilizer Γ (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t) :=
      fun g hg => hre _ t g hg
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  refine ⟨hst, ?_⟩
  obtain ⟨R, hRfin, hR⟩ := hfin
  haveI : Finite ↥R := hRfin.to_subtype
  let V : K.Tup 1 → K.Tup 0 := fun r => K.re (fun _ : Fin 1 => (0 : Fin 2)) r
  haveI : ∀ r : ↥R, Finite ↥(MulAction.stabilizer Γ (V r.1)) := fun r => hstab0 _
  refine ⟨Nat.card (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))), ?_⟩
  intro p hp t ht
  let v : K.Tup 0 := K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t
  let e : Fin (p+1) → K.Tup 1 := fun j => K.re (![0, j] : Fin 2 → Fin (p+1)) t
  have hev : ∀ j, V (e j) = v := fun j => Subtype.ext (funext fun _ => rfl)
  let k : ↥R → Γ := fun r => if h : ∃ g : Γ, g • v = V r.1 then Classical.choose h else 1
  let gsel : Fin (p+1) → Γ := fun j => Classical.choose (hR (e j))
  have hgsel : ∀ j, gsel j • e j ∈ R := fun j => Classical.choose_spec (hR (e j))
  let rsel : Fin (p+1) → ↥R := fun j => ⟨gsel j • e j, hgsel j⟩
  have hgv : ∀ j, gsel j • v = V (rsel j).1 := by
    intro j
    show gsel j • v = gsel j • V (e j)
    rw [hev j]
  have hk : ∀ j, k (rsel j) • v = V (rsel j).1 := by
    intro j
    have hex : ∃ g : Γ, g • v = V (rsel j).1 := ⟨gsel j, hgv j⟩
    have hkj : k (rsel j) = Classical.choose hex := dif_pos hex
    rw [hkj]
    exact Classical.choose_spec hex
  have hmem : ∀ j, gsel j * (k (rsel j))⁻¹ ∈ MulAction.stabilizer Γ (V (rsel j).1) := by
    intro j
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    have h1 : (k (rsel j))⁻¹ • V (rsel j).1 = v := by
      rw [inv_smul_eq_iff]
      exact (hk j).symm
    rw [h1, hgv j]
  let φ : Fin (p+1) → Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1)) :=
    fun j => ⟨rsel j, ⟨gsel j * (k (rsel j))⁻¹, hmem j⟩⟩
  let ψ : (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))) → K.Tup 1 :=
    fun x => ((x.2 : Γ) * k x.1)⁻¹ • x.1.1
  have hψ : ∀ j, ψ (φ j) = e j := by
    intro j
    show ((gsel j * (k (rsel j))⁻¹) * k (rsel j))⁻¹ • (gsel j • e j) = e j
    rw [inv_mul_cancel_right, inv_smul_smul]
  have hinj : Function.Injective φ := by
    intro j j' hjj
    apply ht
    have h1 : e j = e j' := by rw [← hψ j, ← hψ j', hjj]
    have h2 := congrArg (fun x : K.Tup 1 => x.1 1) h1
    exact h2
  have hcard := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AltChainOfPermSplit
section
open CategoryTheory

theorem UpperTheory.altChain_of_permSplit :
    UpperTheory.V.Af.BA.PermSplit → UpperTheory.V.Af.BA.AltChain := by
  intro hP Γ I _ _ K p
  simp only [UpperTheory.V.Af.BA.Cx.alt, UpperTheory.V.Af.BA.Cx.d, Linear.smul_comp, Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum, UpperTheory.V.Af.BA.Cx.reC_comp]
  simp only [Finset.smul_sum, smul_smul]
  set c : ℂ := ((p + 1 + 1).factorial : ℂ)⁻¹ with hc
  have hx : ∀ x : Fin (p + 2),
      ∑ σ : Equiv.Perm (Fin (p + 2)),
        ((-1 : ℂ) ^ (x : ℕ) * (c * (((Equiv.Perm.sign σ : ℤ)) : ℂ))) • K.reC (σ ∘ x.succAbove) =
      ∑ q : Fin (p + 2) × Equiv.Perm (Fin (p + 1)),
        (c * ((-1 : ℂ) ^ (q.1 : ℕ) * ((Equiv.Perm.sign q.2 : ℤ) : ℂ))) • K.reC (q.1.succAbove ∘ q.2) := by
    intro x
    obtain ⟨e, he⟩ := hP (p + 1) x
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl ?_
    rintro ⟨i, τ⟩ -
    obtain ⟨hs, hk⟩ := he i τ
    have hf : (e (i, τ) : Fin (p + 2) → Fin (p + 2)) ∘ x.succAbove = i.succAbove ∘ τ := funext hk
    rw [hf, hs]
    congr 1
    push_cast
    have h1 : (-1 : ℂ) ^ (x : ℕ) * (-1 : ℂ) ^ (x : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    linear_combination (c * (-1 : ℂ) ^ (i : ℕ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) * h1
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  conv_rhs => rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, τ⟩ -
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hF : ((p + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hP2 : ((p : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : p + 2 ≠ 0)
  rw [hc, Nat.factorial_succ (p + 1)]
  push_cast
  field_simp
  ring_nf
  have h2 : (2 + (p : ℂ)) ≠ 0 := by rwa [add_comm]
  field_simp
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PinsOfClosedSubgroupPadicCharacterInv
section
open CategoryTheory

theorem UpperTheory.pins_of_closed_subgroup_padic_character_inv :
    UpperTheory.V.Af.BA.LiftEquiv :=
  _root_.UpperTheory.Reformulated.B.Qe19.pins_of_closed_subgroup_padic_character_inv
end

