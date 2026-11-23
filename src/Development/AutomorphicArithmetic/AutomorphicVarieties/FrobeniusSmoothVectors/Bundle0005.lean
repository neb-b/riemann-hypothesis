module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgVertex
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_vertex :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → HasVertex (ρ.part C) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hC
  have off : ∀ (L : List (F.G0 × Fin n × Fin n)) (j : ℤ),
      (L.map (fun s => w n s.2.1 - w n s.2.2)).sum = j → j ≠ 0 → ∃ s ∈ L, s.2.1 ≠ s.2.2 := by
    intro L j hL hj
    by_contra h
    push_neg at h
    apply hj
    rw [← hL]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    rw [h s hs, sub_self]
  constructor
  · intro x hx
    have hle : ρ.mon 0 ⊆ (LinearMap.range (Algebra.linearMap C K) : Set K) := by
      rintro _ ⟨L, hL, rfl⟩
      by_cases hd : ∃ s ∈ L, s.2.1 ≠ s.2.2
      · obtain ⟨c, -, hc⟩ := hC.cyc L hL hd
        exact ⟨c, hc⟩
      · push_neg at hd
        have hm : (L.map (fun s => ρ.r s.1 s.2.1 s.2.2)).prod ∈ (algebraMap C K).rangeS := by
          apply list_prod_mem
          intro y hy
          obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
          rw [← hd s hs]
          obtain ⟨c, hc, -⟩ := hC.dg s.1 s.2.1
          exact ⟨c, hc⟩
        obtain ⟨c, hc⟩ := hm
        exact ⟨c, hc⟩
    obtain ⟨c, hc⟩ := Submodule.span_le.2 hle hx
    exact ⟨c, hc⟩
  · intro j hj x hx y hy
    open Pointwise in
    have hle : ρ.mon j * ρ.mon (-j) ⊆
        (Submodule.map (Algebra.linearMap C K) (maximalIdeal C) : Set K) := by
      rintro _ ⟨a, ⟨L1, h1, rfl⟩, b, ⟨L2, h2, rfl⟩, rfl⟩
      obtain ⟨s, hs, hne⟩ := off L1 j h1 hj
      obtain ⟨c, hc, hc'⟩ := hC.cyc (L1 ++ L2)
        (by rw [List.map_append, List.sum_append, h1, h2]; ring) ⟨s, List.mem_append_left _ hs, hne⟩
      refine Submodule.mem_map.2 ⟨c, hc, ?_⟩
      rw [Algebra.linearMap_apply, hc', List.map_append, List.prod_append]
    open Pointwise in
    have hxy : x * y ∈ Submodule.span C (ρ.mon j * ρ.mon (-j)) := by
      rw [← Submodule.span_mul_span]
      exact Submodule.mul_mem_mul hx hy
    obtain ⟨c, hc, hc'⟩ := Submodule.mem_map.1 (Submodule.span_le.2 hle hxy)
    exact ⟨c, hc, hc'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgebraMapRangeSpanEqTopOfFiniteGenerators
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.algebraMap_range_span_eq_top_of_finite_generators :
    ∀ {k G M : Type} [Field k] [AddCommGroup M] [Module k M] (Y : Submodule k (G → k)) (C : ℕ) (a : G → M), Module.rank k Y ≤ C → (∀ f : M →ₗ[k] k, (fun g => f (a g)) ∈ Y) → ∃ T : Finset M, T.card ≤ C ∧ ∀ g, a g ∈ Submodule.span k (T : Set M) := by
  intro k G M _ _ _ Y C a hY ha
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent k (Set.range a)
  have hli' : LinearIndepOn k id b := hli
  let B := Module.Basis.extend hli'
  have hmem : ∀ x : b, (x : M) ∈ hli'.extend (Set.subset_univ b) :=
    fun x => hli'.subset_extend (Set.subset_univ b) x.2
  have hB : ∀ x : b, B ⟨x, hmem x⟩ = x := fun x => by
    simp only [B, Module.Basis.coe_extend]
  have hco : ∀ x y : b, B.coord ⟨x, hmem x⟩ (y : M) = if y = x then 1 else 0 := by
    intro x y
    rw [← hB y, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : y = x
    · subst h
      simp
    · have h' : (⟨(y : M), hmem y⟩ : hli'.extend (Set.subset_univ b)) ≠ ⟨x, hmem x⟩ := by
        intro e
        apply h
        apply Subtype.ext
        exact Subtype.mk.inj e
      simp [h, h']
  choose gx hgx using fun x : b => hbs x.2
  let φ : b → Y := fun x => ⟨fun g => B.coord ⟨x, hmem x⟩ (a g), ha (B.coord ⟨x, hmem x⟩)⟩
  have hφ : LinearIndependent k φ := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have h1 := congrArg (fun y : Y => (y : G → k) (gx i)) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ZeroMemClass.coe_zero, Pi.zero_apply, φ, hgx] at h1
    simpa [hco, hi] using h1
  have hcard : Cardinal.mk b ≤ C := hφ.cardinal_le_rank.trans hY
  have hfin : b.Finite := Cardinal.lt_aleph0_iff_set_finite.mp (hcard.trans_lt (Cardinal.natCast_lt_aleph0 (n := C)))
  haveI := hfin.fintype
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.card_toFinset]
    rw [Cardinal.mk_fintype] at hcard
    exact_mod_cast hcard
  · intro g
    rw [Set.Finite.coe_toFinset, hspan]
    exact Submodule.subset_span ⟨g, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zpow_w_ne' {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) : a ^ w n i ≠ a ^ w n j := by
  have h1 : a ≠ 1 := fun h => ha (by rw [h, one_pow])
  have h2 : a ≠ a⁻¹ := fun h => ha (by rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel a)
  have h3 : (1 : kˣ) ≠ a⁻¹ := fun h => h1 (by rw [← inv_inv a, ← h, inv_one])
  rcases hn with rfl | rfl
  · fin_cases i <;> fin_cases j <;> simp_all [UpperTheory.V.Fr.w] <;> simp_all [eq_comm]
  · fin_cases i <;> fin_cases j <;> simp_all [UpperTheory.V.Fr.w] <;> simp_all [eq_comm]

private theorem residue_eq {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {x y : R} (h : res O R x = res O R y) : residue R x = residue R y := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← res_eq_zero_iff O R, map_sub, h, sub_self]

private theorem charpoly_flag' {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : UpperTheory.V.W.HasFlag r.toHomUnits κ) (s : H) :
    (r s).charpoly = ∏ i, (Polynomial.X - Polynomial.C (κ i s : k)) := by
  obtain ⟨g, hg⟩ := h
  have e : ((g * r.toHomUnits s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = (g : Matrix (Fin n) (Fin n) k) * r s * (g : Matrix (Fin n) (Fin n) k)⁻¹ := by
    simp [Matrix.coe_units_inv]
  have hc := Matrix.charpoly_units_conj g (r s)
  rw [← hc, ← e, Matrix.charpoly_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [(hg s).2 i]
  · intro i j hij
    exact (hg s).1 i j hij

theorem UpperTheory.V.Fr.o1 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ v g, (S.u.r (F.loc0 v g)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (S.u.ψ v i g : S.A)) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S v g
  obtain ⟨g₀, hg⟩ := hF.f3 v
  have h4 : ∀ i, res O S.R (S.ρ.ψ v i g₀) = ((F.Ψ (F.loc v g₀) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun i => S.lift.2.1.2 v i g₀
  have hfl : UpperTheory.V.W.HasFlag (S.ρ.r.comp (F.loc0 v)).toHomUnits (S.ρ.ψ v) := by
    refine flag_loc _ _ g₀ (fun i j hij => ?_) ?_ (fun s => S.ρ.ord v s)
    · by_contra hu
      have h2 : (S.ρ.ψ v i g₀ : S.R) - S.ρ.ψ v j g₀ ∈ maximalIdeal S.R := hu
      have h3 := (res_eq_zero_iff O S.R _).2 h2
      rw [map_sub, h4, h4, sub_eq_zero] at h3
      exact zpow_w_ne' hn _ hg i j hij (Units.ext h3)
    · have hd : ((S.ρ.r.comp (F.loc0 v)) g₀).map (residue S.R) =
          Matrix.diagonal fun i => residue S.R (S.ρ.ψ v i g₀) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq]
          refine residue_eq (O := O) ?_
          rw [h4]
          exact S.lift.2.1.1 (F.loc0 v g₀) i
        · rw [Matrix.diagonal_apply_ne _ hij, ← map_zero (residue S.R)]
          refine residue_eq (O := O) ?_
          rw [map_zero]
          exact S.lift.2.2 (F.loc0 v g₀) i j hij
      rw [hd, Matrix.charpoly_diagonal]
  have h := charpoly_flag' _ _ hfl g
  refine Polynomial.map_injective (S.A.val : S.A →+* S.R) Subtype.val_injective ?_
  rw [← Matrix.charpoly_map, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ConjVal
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}

private noncomputable def ee (F : Frame l k) (u : ℤˣ) : F.Γ := if u = 1 then 1 else F.c

private theorem ee_one : ee F 1 = 1 := if_pos rfl

private theorem ee_neg : ee F (-1) = F.c := if_neg (by decide)

private noncomputable def pr (hc : F.del F.c = -1) (s : F.Γ) : F.G0 :=
  ⟨s * ee F (F.del s), by
    rw [MonoidHom.mem_ker, map_mul]
    rcases Int.units_eq_one_or (F.del s) with h | h
    · rw [h, ee_one, map_one, mul_one]
    · rw [h, ee_neg, hc]; simp⟩

private theorem pr_val (hc : F.del F.c = -1) (s : F.Γ) : (pr hc s : F.Γ) = s * ee F (F.del s) := rfl

private theorem pr_coe (hc : F.del F.c = -1) (s : F.G0) : pr hc s = s := by
  apply Subtype.ext
  have h : F.del s = 1 := s.2
  rw [pr_val, h, ee_one, mul_one]

private theorem conj_val (s : F.G0) : (F.conj s : F.Γ) = F.c * s * F.c⁻¹ := rfl

private theorem del_lc (ho : IsOpen (F.del.ker : Set F.Γ)) : IsLocallyConstant F.del := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (F.del.ker : Set F.Γ)) := ho.preimage (by fun_prop)
  filter_upwards [h1.mem_nhds (show x⁻¹ * x ∈ F.del.ker by simp)] with y hy
  have h2 : F.del (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

private theorem pr_cont (hc : F.del F.c = -1) (ho : IsOpen (F.del.ker : Set F.Γ)) : Continuous (pr hc) :=
  Continuous.subtype_mk (continuous_id.mul ((del_lc ho).comp (ee F)).continuous) _

private theorem theta_r {n : ℕ} {C : Type} [CommRing C] (ρ : NRep F n C) (g : F.G0) :
    theta (ρ.r.toHomUnits g) = ρ.r.toHomUnits (F.conj g) := by
  apply Units.ext
  rw [theta_val, ← map_inv, MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits, ← ρ.pol, Frame.star, inv_inv]

private noncomputable def rp (hc : F.del F.c = -1) (hs : F.c * F.c = 1) {n : ℕ} {C : Type} [CommRing C]
    (ρ : NRep F n C) : F.Γ →* GG (m := n) (R := C) where
  toFun s := ⟨ρ.r.toHomUnits (pr hc s), F.del s⟩
  map_one' := by
    have h : pr hc (1 : F.Γ) = 1 := pr_coe hc 1
    ext1
    · simp [h]
    · simp
  map_mul' s t := by
    have hi : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hs
    have hs' : ∀ x, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, hs, one_mul]
    ext1
    · rw [SemidirectProduct.mul_left]
      dsimp only
      rcases Int.units_eq_one_or (F.del s) with h | h
      · rw [h, sgnAct_one, ← map_mul]
        congr 1
        apply Subtype.ext
        rw [Subgroup.coe_mul, pr_val, pr_val, pr_val, map_mul, h, ee_one, one_mul, mul_one, mul_assoc]
      · rw [h, sgnAct_neg_one, theta_r, ← map_mul]
        congr 1
        apply Subtype.ext
        rw [Subgroup.coe_mul, conj_val, pr_val, pr_val, pr_val, map_mul, h, ee_neg, hi]
        rcases Int.units_eq_one_or (F.del t) with h' | h'
        · rw [h', mul_one, ee_neg, ee_one]
          simp only [mul_assoc, mul_one, hs']
        · rw [h', neg_mul_neg, mul_one, ee_neg, ee_one]
          simp only [mul_assoc, mul_one, hs', hs]
    · simp

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_box :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (I : Ideal C) (ρ : NRep F n C), ρ.Cont I → (∀ v, UpperTheory.V.W.HasFlag (ρ.r.comp (F.loc0 v)).toHomUnits (ρ.ψ v)) → ∃ B : Box F n C, B.Of ρ ∧ B.Cont I := by
  intro l _ k _ _ F C₀ n hF C _ I ρ hc hf
  choose g hg using hf
  have hm : ∀ s, (rp hF.del_c hF.c_sq ρ s).mat = ρ.r (pr hF.del_c s) := fun s => rfl
  refine ⟨⟨rp hF.del_c hF.c_sq ρ, fun s => rfl, g, fun v s i j h => ?_⟩, ⟨?_, fun s => ?_, fun v i s => ?_⟩,
    fun i j N => ?_⟩
  · have e : pr hF.del_c (F.loc v s) = F.loc0 v s := pr_coe hF.del_c (F.loc0 v s)
    rw [hm, e]
    exact (hg v s).1 i j h
  · have e : pr hF.del_c F.c = 1 := by
      apply Subtype.ext
      rw [pr_val, hF.del_c, ee_neg, hF.c_sq]
      rfl
    show (rp hF.del_c hF.c_sq ρ F.c).mat = 1
    rw [hm, e, map_one]
  · show (rp hF.del_c hF.c_sq ρ s).mat = _
    rw [hm, pr_coe]
  · exact (hg v s).2 i
  · exact (hc.1 i j N).comp_continuous (pr_cont hF.del_c hF.del_open)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpBasis
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem par_equiv {ι : Type} [Fintype ι] (v : ι → ZMod 2) :
    ∃ (a g : ℕ) (e : Fin a ⊕ Fin g ≃ ι), ∀ s, v (e s) = Space.Loc.par a g s := by
  classical
  refine ⟨_, _, (Equiv.sumCongr (Fintype.equivFin {i // v i = 0}).symm
    (Fintype.equivFin {i // ¬ v i = 0}).symm).trans (Equiv.sumCompl fun i => v i = 0), ?_⟩
  have h2 : ∀ j : ZMod 2, ¬ j = 0 → j = 1 := by decide
  rintro (s | s)
  · exact ((Fintype.equivFin {i // v i = 0}).symm s).2
  · exact h2 _ ((Fintype.equivFin {i // ¬ v i = 0}).symm s).2

theorem UpperTheory.V.Fr.ep_basis :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ J N : Ideal R, (∀ y ∈ J, σ y ∈ J) → (∀ y ∈ N, σ y ∈ N) → maximalIdeal R * J ≤ N → ∃ (a g : ℕ) (z : Fin a ⊕ Fin g → R), (∀ s, z s ∈ J ∧ z s ∈ evp σ (Space.Loc.par a g s)) ∧ J ≤ Ideal.span (Set.range z) ⊔ N ∧ ∀ c : Fin a ⊕ Fin g → O, ∑ s, c s • z s ∈ N → ∀ s, c s ∈ maximalIdeal O := by
  classical
  intro O _ _ _ _ h2 R _ _ _ σ hσ J N hJ hN hmJ
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian J : J.FG)
  obtain ⟨u, hu2, hucomm⟩ : ∃ u : R, u * 2 = 1 ∧ ∀ x, σ (u * x) = u * σ x :=
    ⟨algebraMap O R ↑h2.unit⁻¹, by
      rw [← map_ofNat (algebraMap O R) 2, ← map_mul, h2.val_inv_mul, map_one],
      fun x => by rw [map_mul, AlgHom.commutes]⟩
  have hsg : ∀ p : ZMod 2, sg R p * sg R p = 1 := by
    intro p
    simp only [sg, ← pow_add, ← two_mul, pow_mul]
    simp
  have hsgσ : ∀ p : ZMod 2, σ (sg R p) = sg R p := by
    intro p
    simp [sg]
  have s0 : sg R 0 = 1 := by simp [sg]
  have s1 : sg R 1 = -1 := by
    show (-1 : R) ^ ((1 : ZMod 2).val) = -1
    rw [show (1 : ZMod 2).val = 1 from rfl]
    simp
  let w : T × ZMod 2 → R := fun j => u * (j.1.1 + sg R j.2 * σ j.1.1)
  have hwJ : ∀ j, w j ∈ J := by
    intro j
    have ht : (j.1 : R) ∈ J := hT ▸ Submodule.subset_span j.1.2
    exact J.mul_mem_left _ (J.add_mem ht (J.mul_mem_left _ (hJ _ ht)))
  have hwev : ∀ j, w j ∈ evp σ j.2 := by
    intro j
    show σ (w j) = sg R j.2 * w j
    simp only [w, hucomm, map_add (f := _), map_mul, hσ, hsgσ]
    linear_combination (-(u * σ j.1.1)) * hsg j.2
  have hmemN : ∀ c ∈ maximalIdeal O, ∀ y ∈ J, c • y ∈ N := by
    intro c hc y hy
    rw [Algebra.smul_def]
    exact hmJ (Ideal.mul_mem_mul (map_nonunit (algebraMap O R) c hc) hy)
  let Indep : Finset (T × ZMod 2) → Prop := fun S =>
    ∀ c : T × ZMod 2 → O, ∑ s ∈ S, c s • w s ∈ N → ∀ s ∈ S, c s ∈ maximalIdeal O
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image
    (Finset.univ.powerset.filter Indep) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨by simp, fun c _ s hs => absurd hs (Finset.notMem_empty s)⟩⟩
  have hS' : Indep S := (Finset.mem_filter.mp hS).2
  obtain ⟨a, g, e, he⟩ := par_equiv (ι := S) (fun i => i.1.2)
  refine ⟨a, g, fun s => w (e s).1, ?_, ?_, ?_⟩
  · intro s
    refine ⟨hwJ _, ?_⟩
    rw [← he s]
    exact hwev _
  · have hspan : ∀ j, w j ∈ Ideal.span (Set.range fun s => w (e s).1) ⊔ N := by
      intro j
      by_cases hj : j ∈ S
      · exact Ideal.mem_sup_left (Ideal.subset_span ⟨e.symm ⟨j, hj⟩, by simp⟩)
      · have hnot : ¬ Indep (insert j S) := by
          intro hI
          have := hmax (insert j S) (Finset.mem_filter.mpr ⟨by simp, hI⟩)
          rw [Finset.card_insert_of_notMem hj] at this
          omega
        simp only [Indep, not_forall] at hnot
        obtain ⟨c, hc, s, hs, hcs⟩ := hnot
        rw [Finset.sum_insert hj] at hc
        have hcj : c j ∉ maximalIdeal O := by
          intro hcj
          have h1 : c j • w j ∈ N := hmemN _ hcj _ (hwJ j)
          have h2' : ∑ s ∈ S, c s • w s ∈ N := by
            have := N.sub_mem hc h1
            simpa using this
          rcases Finset.mem_insert.mp hs with rfl | hs
          · exact hcs hcj
          · exact hcs (hS' c h2' s hs)
        have hunit : IsUnit (c j) := by
          by_contra h
          exact hcj ((IsLocalRing.mem_maximalIdeal _).mpr h)
        have hsumS : ∑ s ∈ S, c s • w s ∈ Ideal.span (Set.range fun s => w (e s).1) := by
          refine Ideal.sum_mem _ fun s hs => ?_
          rw [Algebra.smul_def]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e.symm ⟨s, hs⟩, by simp⟩)
        have hcw : c j • w j ∈ Ideal.span (Set.range fun s => w (e s).1) ⊔ N := by
          have : c j • w j = (c j • w j + ∑ s ∈ S, c s • w s) - ∑ s ∈ S, c s • w s := by
            abel
          rw [this]
          exact Submodule.sub_mem _ (Ideal.mem_sup_right hc) (Ideal.mem_sup_left hsumS)
        obtain ⟨d, hd⟩ := hunit.exists_left_inv
        have : w j = d • (c j • w j) := by rw [smul_smul, hd, one_smul]
        rw [this, Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hcw
    rw [← hT]
    show Submodule.span R (T : Set R) ≤ _
    rw [Submodule.span_le]
    intro t ht
    have : t = w (⟨t, ht⟩, 0) + w (⟨t, ht⟩, 1) := by
      simp only [w, s0, s1]
      linear_combination (-t) * hu2
    rw [this]
    exact Submodule.add_mem _ (hspan _) (hspan _)
  · intro c hc s
    let c' : T × ZMod 2 → O := fun j => if h : j ∈ S then c (e.symm ⟨j, h⟩) else 0
    have hsum : ∑ j ∈ S, c' j • w j = ∑ s, c s • w (e s).1 := by
      rw [← Finset.sum_coe_sort S, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp [c']
    have := hS' c' (hsum ▸ hc) (e s).1 (e s).2
    simpa [c'] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpOddSpanX
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ep_odd_span_X {O σ ι : Type} [CommRing O] (e : ι → σ) (s : Finset ι) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n (e i) = 0) → MvPowerSeries.coeff n f = 0) →
      f ∈ Ideal.span (Set.range fun i => (MvPowerSeries.X (e i) : MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X e s

theorem UpperTheory.V.Fr.ep_odd :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (P : GPres O σ), Ideal.span (evp σ 1 : Set R) = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (.inr i))) := by
  intro O _ _ R _ _ _ σ P
  classical
  rw [← P.part 1]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h1 : f ∈ Ideal.span (Set.range fun i : Fin P.g =>
        (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin P.a ⊕ Fin P.g) O)) := by
      refine ep_odd_span_X Sum.inr Finset.univ f fun n hn => hf n ?_
      have : Finsupp.weight (Space.Loc.par P.a P.g) n = 0 := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        refine Finset.sum_eq_zero fun s _ => ?_
        rcases s with s | s
        · simp [Space.Loc.par]
        · simp [hn s (Finset.mem_univ _)]
      rw [this]
      decide
    have h2 := Ideal.mem_map_of_mem P.p h1
    rw [Ideal.map_span, ← Set.range_comp] at h2
    exact h2
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine Ideal.subset_span ⟨MvPowerSeries.X (.inr i), fun n hn => ?_, rfl⟩
    rw [MvPowerSeries.coeff_X, if_neg]
    rintro rfl
    apply hn
    simp [Finsupp.weight_single, Space.Loc.par]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerMemCone
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.frobenius_corner_mem_cone :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F 3 K) (σ : NRep F 2 K), IsCorner ρ σ → Cone O C ρ → Cone O C σ := by
  intro l _ O _ _ F C _ _ _ K _ _ ρ σ hc hC
  have cinj : Function.Injective cor := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [cor]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g i
    obtain ⟨c, h1, h2⟩ := hC.dg g (cor i)
    exact ⟨c, by rw [h1, hc.r], by rw [h2, w_cor]⟩
  · intro L hs hne
    have hs' : (List.map (fun s => w 3 s.2.1 - w 3 s.2.2) (L.map fun s => (s.1, cor s.2.1, cor s.2.2))).sum = 0 := by
      rw [← hs, List.map_map]
      congr 1
      apply List.map_congr_left
      intro s _
      simp [w_cor]
    have hne' : ∃ s ∈ L.map (fun s => (s.1, cor s.2.1, cor s.2.2)), s.2.1 ≠ s.2.2 := by
      obtain ⟨s, hs1, hs2⟩ := hne
      exact ⟨(s.1, cor s.2.1, cor s.2.2), List.mem_map_of_mem hs1, fun h => hs2 (cinj h)⟩
    obtain ⟨c, hcm, he⟩ := hC.cyc _ hs' hne'
    refine ⟨c, hcm, ?_⟩
    rw [he, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s _
    simp [hc.r]
  · intro i j
    simp only [hc.r]
    exact hC.fg _ _
  · intro i j N
    have e : (fun g => σ.r g i j) = fun g => ρ.r g (cor i) (cor j) := funext fun g => hc.r g i j
    have h := hC.cont (cor i) (cor j) N
    rw [← e] at h
    have e3 : (fun g => (maximalIdeal C ^ N • Submodule.span C (Set.range fun g => σ.r g i j)).mkQ (σ.r g i j)) =
        fun g => (maximalIdeal C ^ N • Submodule.span C (Set.range fun g => σ.r g i j)).mkQ (ρ.r g (cor i) (cor j)) :=
      funext fun g => by rw [hc.r]
    rw [e3]
    exact h
  · obtain ⟨χ, hχ, hχρ⟩ := hC.psi
    refine ⟨fun v i g => χ v (cor i) g, fun v i => ⟨(hχ v (cor i)).1, fun g => ?_⟩, fun v i g => ?_⟩
    · rw [(hχ v (cor i)).2 g, w_cor]
    · rw [hχρ, hc.ψ]
end

