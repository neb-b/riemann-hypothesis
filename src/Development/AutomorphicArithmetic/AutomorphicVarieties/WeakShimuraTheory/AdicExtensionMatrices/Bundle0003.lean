module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PreImage
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem adjoin_top_of_tower {B B' A : Type} [CommRing B] [CommRing B'] [CommRing A] [Algebra B A] [Algebra B B']
    [Algebra B' A] [IsScalarTower B B' A] {s : Set A} (h : Algebra.adjoin B s = ⊤) : Algebra.adjoin B' s = ⊤ := by
  have h1 : Algebra.adjoin B s ≤ (Algebra.adjoin B' s).restrictScalars B :=
    Algebra.adjoin_le fun x hx => (Subalgebra.mem_restrictScalars B).2 (Algebra.subset_adjoin hx)
  rw [h] at h1
  exact eq_top_iff.2 fun x _ => (Subalgebra.mem_restrictScalars B).1 (h1 Algebra.mem_top)

private theorem pre_of_surj {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a) [Nontrivial Y.A] (B' : Type) [CommRing B'] [Algebra Λ B']
    (p : Y.B →ₐ[Λ] B') (hp : Function.Surjective p) (j : B' →+* Y.A) (hj : ∀ b, j (p b) = algebraMap Y.B Y.A b)
    (hi : Function.Injective j) : ∃ Y' : Pre Φ a, Function.Injective (algebraMap Y'.B Y'.A) := by
  have hp' : Function.Surjective (p : Y.B →+* B') := hp
  haveI : Nontrivial B' := j.domain_nontrivial
  haveI : IsCO Λ B' := co_quot Λ Y.B B' p hp
  letI : Algebra B' Y.A := j.toAlgebra
  letI : Algebra Y.B B' := (p : Y.B →+* B').toAlgebra
  haveI t1 : IsScalarTower Y.B B' Y.A := IsScalarTower.of_algebraMap_eq fun b => (hj b).symm
  haveI t2 : IsScalarTower Λ B' Y.A := IsScalarTower.of_algebraMap_eq fun b => by
    rw [← p.commutes, IsScalarTower.algebraMap_apply Λ Y.B Y.A]
    exact (hj _).symm
  have hm : (maximalIdeal Y.B).map (p : Y.B →+* B') = maximalIdeal B' :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hp'
  have hle : maximalIdeal Y.B ≤ (maximalIdeal B').comap (p : Y.B →+* B') := by
    rw [← hm]; exact Ideal.le_comap_map
  have hc : (algebraMap B' Y.A).comp (p : Y.B →+* B') = algebraMap Y.B Y.A := RingHom.ext hj
  have hr : (res Λ B' : B' →+* ResidueField Λ).comp (p : Y.B →+* B') =
      (res Λ Y.B : Y.B →+* ResidueField Λ) := RingHom.ext fun b => res_map (O := Λ) (R := Y.B) p b
  haveI := Y.ft
  refine ⟨{ A := Y.A, B := B', ft := Algebra.FiniteType.of_restrictScalars_finiteType Y.B _ _
            P := Y.P, pair := Y.pair, cont := ?_, gen := adjoin_top_of_tower Y.gen
            cp := fun g => (Y.cp g).map (p : Y.B →+* B')
            cp_map := fun g => ?_, cp_cont := fun n => ?_, cp_red := fun g => ?_
            ψ := fun v i s => p (Y.ψ v i s)
            ψ_map := fun v i s hs => (hj _).trans (Y.ψ_map v i s hs)
            ψ_cont := fun v i => adicCont_map (p : Y.B →+* B') hle (Y.ψ_cont v i)
            ψ_red := fun v i s hs => (res_map (O := Λ) (R := Y.B) p _).trans (Y.ψ_red v i s hs)
            genB := fun R _ _ _ f f' h1 h2 => ?_
            univ := Y.univ }, hi⟩
  · rw [← hm, Ideal.map_map, hc]
    exact Y.cont
  · rw [Polynomial.map_map, hc, Y.cp_map]
  · simp only [coeff_map]
    exact adicCont_map (p : Y.B →+* B') hle (Y.cp_cont n)
  · rw [Polynomial.map_map, hr, Y.cp_red]
  · have h : f.comp p = f'.comp p := Y.genB R _ _ (fun g n => by
      have h3 := h1 g n
      rw [coeff_map] at h3
      exact h3) h2
    refine AlgHom.ext fun x => ?_
    obtain ⟨b, rfl⟩ := hp x
    exact AlgHom.congr_fun h b

theorem UpperTheory.V.Ws.sxPreImage :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a), Nontrivial Y.A → ∃ Y' : Pre Φ a, Function.Injective (algebraMap Y'.B Y'.A) := by
  intro O Γ _ _ _ Φ Λ _ _ a Y hA
  exact pre_of_surj Y (Y.B ⧸ RingHom.ker (algebraMap Y.B Y.A)) (Ideal.Quotient.mkₐ Λ _) Ideal.Quotient.mk_surjective
    (RingHom.kerLift (algebraMap Y.B Y.A)) (fun b => RingHom.kerLift_mk _ b) (RingHom.kerLift_injective _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ScaleRD
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem wt_add' (i j k : Fin 4) : wt i j + wt j k = wt i k := by
  simp [wt]

private theorem laurent_mul_apply_eq_single_of_entries_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (X Y : M4 S) (X0 Y0 : M4 R)
    (hX : ∀ i j, e (X i j) = HahnSeries.single (τ (wt i j)) (X0 i j))
    (hY : ∀ i j, e (Y i j) = HahnSeries.single (τ (wt i j)) (Y0 i j)) (i j : Fin 4) :
    e ((X * Y) i j) = HahnSeries.single (τ (wt i j)) ((X0 * Y0) i j) := by
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [map_add e, map_mul, hX, hY, HahnSeries.single_mul_single, ← map_add τ, wt_add',
    HahnSeries.single_add]

private theorem laurent_adj_apply_eq_single_of_entries_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (X : M4 S) (X0 : M4 R)
    (hX : ∀ i j, e (X i j) = HahnSeries.single (τ (wt i j)) (X0 i j)) (i j : Fin 4) :
    e ((adj X) i j) = HahnSeries.single (τ (wt i j)) ((adj X0) i j) := by
  have hrev : ∀ i j : Fin 4, wt j.rev i.rev = wt i j := by decide
  simp only [adj, Matrix.of_apply, zsmul_eq_mul, map_mul, map_intCast, hX, hrev]
  rw [← map_intCast (HahnSeries.C : R →+* LaurentSeries R), HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add]

private theorem laurent_smul_one_apply_eq_single_of_eq_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (ν : S) (ν0 : R) (hν : e ν = HahnSeries.single 0 ν0) (i j : Fin 4) :
    e ((ν • (1 : M4 S)) i j) = HahnSeries.single (τ (wt i j)) ((ν0 • (1 : M4 R)) i j) := by
  have hw0 : ∀ i : Fin 4, wt i i = 0 := by decide
  by_cases h : i = j
  · subst h
    simp [Matrix.smul_apply, hν, hw0]
  · simp [Matrix.smul_apply, Matrix.one_apply_ne h]

theorem UpperTheory.V.Ws.sxScaleRD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R} {τ : ℤ × ℤ →+ ℤ} {D : RD Φ R}, IsNilpotent (maximalIdeal R) → Laur (Λ := Λ) c e → (∀ i j, -(c : ℤ) ≤ τ (wt i j)) → Φ.Near a τ D → ∃ D' : RD Φ S, Φ.Near a 0 D' ∧ (∀ g i j, e (D'.r g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j)) ∧ ∀ v i s, e (D'.ψ v i s) = HahnSeries.single 0 (D.ψ v i s) := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ S _ _ _ c e τ D hnil hL hc hN
  classical
  have hw0 : ∀ i : Fin 4, wt i i = 0 := by decide
  have hresm : ∀ {T : Type} [CommRing T] [Algebra Λ T] [IsCO Λ T] (y : T), y ∈ maximalIdeal T →
      res Λ T y = 0 := by
    intro T _ _ _ y hy
    simp [res, (IsLocalRing.residue_eq_zero_iff y).mpr hy]
  have hex0 : ∀ x : R, ∃ y : S, e y = HahnSeries.single 0 x ∧ res Λ S y = res Λ R x := by
    intro x
    obtain ⟨l, hl⟩ := IsCO.res_surj (O := Λ) x
    obtain ⟨y, hy, hye⟩ := hL.mem 0 _ (Or.inr ⟨by omega, hl⟩)
    refine ⟨y + algebraMap Λ S l, ?_, ?_⟩
    · rw [map_add (f := _), hye, hL.alg, ← HahnSeries.single_add, sub_add_cancel]
    · rw [map_add (f := _), hresm y hy, AlgHom.commutes, zero_add]
      conv_rhs => rw [← sub_add_cancel x (algebraMap Λ R l)]
      rw [map_add (f := _), hresm _ hl, AlgHom.commutes, zero_add]
  have hent : ∀ g i j, ∃ y, e y = HahnSeries.single (τ (wt i j)) (D.r g i j) := by
    intro g i j
    rcases lt_trichotomy (τ (wt i j)) 0 with h | h | h
    · have hij : i ≠ j := by
        rintro rfl
        rw [hw0, map_zero] at h
        exact lt_irrefl _ h
      obtain ⟨y, -, hy⟩ := hL.mem _ _ (Or.inr ⟨hc i j, hN.off g i j hij h.le⟩)
      exact ⟨y, hy⟩
    · rw [h]
      obtain ⟨y, hy, -⟩ := hex0 (D.r g i j)
      exact ⟨y, hy⟩
    · obtain ⟨y, -, hy⟩ := hL.mem _ _ (Or.inl h)
      exact ⟨y, hy⟩
  have hmem : ∀ g i j, i ≠ j → ∀ y, e y = HahnSeries.single (τ (wt i j)) (D.r g i j) →
      y ∈ maximalIdeal S := by
    intro g i j hij y hy
    rcases le_or_gt (τ (wt i j)) 0 with h | h
    · obtain ⟨y', hy', he'⟩ := hL.mem _ _ (Or.inr ⟨hc i j, hN.off g i j hij h⟩)
      rw [hL.inj (hy.trans he'.symm)]
      exact hy'
    · obtain ⟨y', hy', he'⟩ := hL.mem _ _ (Or.inl h)
      rw [hL.inj (hy.trans he'.symm)]
      exact hy'
  let pre : LaurentSeries R → S := fun z => if h : ∃ y, e y = z then h.choose else 0
  have hpre : ∀ z, (∃ y, e y = z) → e (pre z) = z := by
    intro z h
    simp only [pre, dif_pos h]
    exact h.choose_spec
  have hpre0 : ∀ x : R, e (pre (HahnSeries.single 0 x)) = HahnSeries.single 0 x := by
    intro x
    obtain ⟨y, hy, -⟩ := hex0 x
    exact hpre _ ⟨y, hy⟩
  have hres0 : ∀ x : R, res Λ S (pre (HahnSeries.single 0 x)) = res Λ R x := by
    intro x
    obtain ⟨y, hy, hr⟩ := hex0 x
    rw [hL.inj ((hpre0 x).trans hy.symm)]
    exact hr
  let rr : Γ → M4 S := fun g => Matrix.of fun i j => pre (HahnSeries.single (τ (wt i j)) (D.r g i j))
  have hrr : ∀ g i j, e (rr g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j) :=
    fun g i j => hpre _ (hent g i j)
  have hext : ∀ X Y : M4 S, (∀ i j, e (X i j) = e (Y i j)) → X = Y :=
    fun X Y h => Matrix.ext fun i j => hL.inj (h i j)
  have h1 : ∀ i j, e ((1 : M4 S) i j) = HahnSeries.single (τ (wt i j)) ((1 : M4 R) i j) := by
    intro i j
    have := laurent_smul_one_apply_eq_single_of_eq_single e τ 1 1 (by rw [map_one, HahnSeries.single_zero_one]) i j
    simpa only [one_smul] using this
  let r' : Γ →* M4 S :=
    { toFun := rr
      map_one' := hext _ _ fun i j => by rw [hrr, D.r.map_one, h1]
      map_mul' := fun g h => hext _ _ fun i j => by
        rw [hrr, D.r.map_mul, laurent_mul_apply_eq_single_of_entries_single e τ _ _ _ _ (hrr g) (hrr h)] }
  have hr' : ∀ g i j, e (r' g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j) := hrr
  let ψ' : (v : Φ.ι) → Fin 4 → ↥(Φ.Gv v) →* S := fun v i =>
    { toFun := fun s => pre (HahnSeries.single 0 (D.ψ v i s))
      map_one' := hL.inj (by rw [hpre0, (D.ψ v i).map_one, HahnSeries.single_zero_one, map_one])
      map_mul' := fun s t => hL.inj (by
        rw [hpre0, (D.ψ v i).map_mul, map_mul e, hpre0, hpre0, HahnSeries.single_mul_single, zero_add]) }
  obtain ⟨K, hK⟩ := hnil
  have hinj : Function.Injective (Ideal.Quotient.mk (maximalIdeal R ^ K)) := by
    intro x y h
    rwa [Ideal.Quotient.eq, hK, Ideal.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at h
  refine ⟨⟨r', ψ'⟩, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hr', fun v i s => hpre0 _⟩
  · intro g
    have hg : adj (D.r g) * D.r g = _ := hN.rep.mult g
    show adj (r' g) * r' g = _
    simp only [RingHom.comp_apply] at hg ⊢
    refine hext _ _ fun i j => ?_
    rw [laurent_mul_apply_eq_single_of_entries_single e τ _ _ _ _ (laurent_adj_apply_eq_single_of_entries_single e τ _ _ (hr' g)) (hr' g), hg,
      laurent_smul_one_apply_eq_single_of_eq_single e τ _ _ (hL.alg _)]
  · intro g hg
    refine hext _ _ fun i j => ?_
    rw [hr', hN.rep.kill g hg, h1]
  · intro i j hij
    apply hL.inj
    rw [hr', hN.rep.nrm hij, HahnSeries.single_eq_zero, map_zero]
  · intro i j N
    have h2 : IsLocallyConstant fun g => D.r g i j :=
      IsLocallyConstant.desc _ _ (hN.cont i j K) hinj
    exact h2.comp (fun x => Ideal.Quotient.mk (maximalIdeal S ^ N) (pre (HahnSeries.single (τ (wt i j)) x)))
  · intro v i N
    have h2 : IsLocallyConstant fun s => D.ψ v i s :=
      IsLocallyConstant.desc _ _ (hN.contψ v i K) hinj
    exact h2.comp (fun x => Ideal.Quotient.mk (maximalIdeal S ^ N) (pre (HahnSeries.single 0 x)))
  · intro g i
    rw [← hN.diag g i]
    show res Λ S (pre (HahnSeries.single (τ (wt i i)) (D.r g i i))) = _
    rw [hw0, map_zero]
    exact hres0 _
  · intro g i j hij _
    exact hmem g i j hij _ (hr' g i j)
  · intro v i s
    rw [← hN.redψ v i s]
    exact hres0 _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxCpRes
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cp_low {R : Type} [CommRing R] (M : M4 R) (σ : Equiv.Perm (Fin 4))
    (h : ∀ i j, i < j → M (σ i) (σ j) = 0) : M.charpoly = ∏ i, (X - C (M i i)) := by
  have h1 : (Matrix.reindex σ.symm σ.symm M).charpoly = M.charpoly := Matrix.charpoly_reindex _ _
  rw [← h1, ← Matrix.charpoly_transpose, Matrix.charpoly_of_upperTriangular]
  · simpa using Equiv.prod_comp σ fun i => X - C (M i i)
  · intro i j hij
    simpa using h j i hij

theorem UpperTheory.V.Ws.sxCpRes :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R : Type} [CommRing R] (a : O →+* R) (P : PD Φ.ι Γ R), Φ.Res a P → ∀ g, (P.r g).charpoly = ∏ i, (X - C (a (Φ.χ i g))) := by
  intro O Γ _ _ Φ R _ a P h g
  simp only [← h.diag g]
  rcases h.shape with ⟨h1, -⟩ | h1
  · refine cp_low _ (Equiv.swap 1 2) fun i j hij => h1 g _ _ ?_ ?_
    · exact fun e => hij.ne ((Equiv.swap 1 2).injective e)
    · revert i j; decide
  · refine cp_low _ 1 fun i j hij => h1 g _ _ hij.ne ?_
    revert i j; decide
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxExtGr0
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxExtGr0 :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO Λ (W.gr 0)] (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.gr 0 →ₐ[Λ] R'), (∀ (b : W.gr 0) (n : W.σ →₀ ℕ), Finsupp.weight W.wt n = 0 → ((b : W.A) : R) = (n.prod fun s k => W.z s ^ k) → f b = f' b) → f = f' := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz _ R' _ _ _ f f' h
  obtain ⟨-, u, hu, hm⟩ := UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials Λ X R W hz
  have hloc : ∀ g : W.gr 0 →ₐ[Λ] R', ∀ x ∈ maximalIdeal (W.gr 0), g x ∈ maximalIdeal R' := fun g x hx => by
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hx
  refine UpperTheory.V.Alg.co_ext Λ (W.gr 0) Λ R' (maximalIdeal R') (Algebra.ofId Λ (W.gr 0)) (u : Set (W.gr 0)) ?_ ?_ f f'
    ⟨1, fun x hx => ?_⟩ (Subsingleton.elim _ _) fun s hs => ?_
  · intro b hb
    show b ∈ maximalIdeal (W.gr 0)
    rw [hm]
    exact Ideal.mem_sup_right (Ideal.subset_span hb)
  · refine le_trans (hm.trans (sup_comm _ _)).le ?_
    exact le_sup_left
  · rw [pow_one] at hx
    exact ⟨hloc f x hx, hloc f' x hx⟩
  · obtain ⟨n, -, hn, hb⟩ := hu s hs
    exact h s n hn hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxSubRD
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxSubRD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {Λ R : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] (a : O →+* Λ) (A : Subalgebra Λ R) (D : RD Φ R), (∀ g i j, D.r g i j ∈ A) → (∀ v i s, D.ψ v i s ∈ A) → Φ.IsRep ((algebraMap Λ R).comp a) D.r → ∃ D' : RD Φ A, D'.map (A.val : A →+* R) = D ∧ Φ.IsRep ((algebraMap Λ A).comp a) D'.r := by
  intro O Γ _ _ Φ Λ R _ _ _ a A D hr hψ h
  have h1 : ∀ i j : Fin 4, (((1 : M4 A) i j : A) : R) = (1 : M4 R) i j := fun i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  let r' : Γ →* M4 A :=
    { toFun := fun g => Matrix.of fun i j => ⟨D.r g i j, hr g i j⟩
      map_one' := by
        ext i j
        rw [h1]; simp
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  have hr' : ∀ g i j, ((r' g i j : A) : R) = D.r g i j := fun _ _ _ => rfl
  refine ⟨⟨r', fun v i => (D.ψ v i).codRestrict A (hψ v i)⟩, ?_, fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩
  · refine RD.ext ?_ ?_
    · ext g i j; rfl
    · funext v i; ext s; rfl
  · have := h.mult g
    unfold IsGSp at this ⊢
    ext i j
    have e := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul, MulMemClass.coe_mul, h1]
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    refine Eq.trans ?_ e
    simp [Matrix.mul_apply, adj, hr']
  · ext i j
    rw [h1]
    show D.r g i j = _
    rw [h.kill g hg]
  · exact Subtype.ext (h.nrm hij)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxZMono
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def Pm {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] (r : Γ →* M4 R) (E : Subalgebra Λ R)
    (w : ℤ × ℤ) (x : R) : Prop := ∃ e ∈ E, ∃ m ∈ mono r w, x = e * m

private theorem Pm_mem {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] (r : Γ →* M4 R) (E : Subalgebra Λ R)
    {x : R} (hx : x ∈ E) : Pm r E 0 x := ⟨x, hx, 1, ⟨[], by simp, by simp⟩, by simp⟩

private theorem Pm_mul {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] {r : Γ →* M4 R} {E : Subalgebra Λ R}
    {w w' : ℤ × ℤ} {x y : R} (hx : Pm r E w x) (hy : Pm r E w' y) : Pm r E (w + w') (x * y) := by
  obtain ⟨e, he, m, ⟨L, hL, rfl⟩, rfl⟩ := hx
  obtain ⟨e', he', m', ⟨L', hL', rfl⟩, rfl⟩ := hy
  refine ⟨e * e', mul_mem he he', _, ⟨L ++ L', by rw [List.map_append, List.sum_append, hL, hL'], rfl⟩, ?_⟩
  rw [List.map_append, List.prod_append]
  ring

private theorem Pm_pow {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] {r : Γ →* M4 R} {E : Subalgebra Λ R}
    {w : ℤ × ℤ} {x : R} (hx : Pm r E w x) (k : ℕ) : Pm r E (k • w) (x ^ k) := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; exact Pm_mem r E (one_mem E)
  | succ k ih => rw [succ_nsmul, pow_succ]; exact Pm_mul ih hx

theorem UpperTheory.V.Ws.sxZMono :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R} (E : Subalgebra Λ R), RD.Graded D W → mono D.r 0 ⊆ E → (∀ v i s, D.ψ v i s ∈ E) → ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = 0 → (n.prod fun s k => W.z s ^ k) ∈ E := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ R _ _ _ D W E hG hm hψ n hn
  have hz : ∀ s, Pm D.r E (W.wt s) (W.z s) := by
    intro s
    rcases hG.var s with ⟨g, i, j, c, h1, h2, h3⟩ | ⟨v, i, t, c, h1, h2⟩
    · have hmem : D.r g i j ∈ mono D.r (wt i j) := ⟨[(g, i, j)], by simp, by simp⟩
      by_cases hij : i = j
      · have h0 : wt i j = 0 := (wt_eq_zero i j).2 hij
        rw [h2, h1, h0]
        rw [h0] at hmem
        exact Pm_mem _ _ (sub_mem (hm hmem) (E.algebraMap_mem c))
      · rw [h2, h1, h3 hij, map_zero, sub_zero]
        exact ⟨1, one_mem E, _, hmem, (one_mul _).symm⟩
    · rw [h2, h1]
      exact Pm_mem _ _ (sub_mem (hψ v i t) (E.algebraMap_mem c))
  have key : ∀ n : W.σ →₀ ℕ, Pm D.r E (Finsupp.weight W.wt n) (n.prod fun s k => W.z s ^ k) := by
    intro n
    induction n using Finsupp.induction_linear with
    | zero => rw [map_zero, Finsupp.prod_zero_index]; exact Pm_mem _ _ (one_mem E)
    | add f g hf hg =>
      rw [map_add (f := _), Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      exact Pm_mul hf hg
    | single s k =>
      rw [Finsupp.prod_single_index (h := fun s k => W.z s ^ k) (pow_zero _), Finsupp.weight_single]
      exact Pm_pow (hz s) k
  obtain ⟨e, he, m, hm', h⟩ := key n
  rw [h]
  rw [hn] at hm'
  exact mul_mem he (hm hm')
end

