module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Data.Finsupp.WellFounded

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite
section
noncomputable section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun {f} hf => ?_⟩
  have hc : ∀ i : Fin r, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (f := fun n => f n i) ?_
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    rw [mem_smul_top_pi] at h
    have := h i
    simpa [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top] using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := hL i n
  rw [SModEq.sub_mem] at this
  simpa [smul_eq_mul, Ideal.mul_top] using this

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, φ, hφ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  have himg : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R M) = Submodule.map φ (I ^ n • ⊤) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hφ]
  refine ⟨fun {f} hf => ?_⟩
  have hmem : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M) := by
    intro n
    have := SModEq.sub_mem.1 (hf (Nat.le_succ n))
    rw [← neg_sub]
    exact neg_mem this
  have hd : ∀ n, ∃ d : Fin r → R, d ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)) ∧ φ d = f (n + 1) - f n := by
    intro n
    have := hmem n
    rw [himg n, Submodule.mem_map] at this
    exact this
  choose d hdmem hdφ using hd
  obtain ⟨y0, hy0⟩ := hφ (f 0)
  set g : ℕ → (Fin r → R) := fun n => y0 + ∑ k ∈ Finset.range n, d k with hg
  have hgφ : ∀ n, φ (g n) = f n := by
    intro n
    induction n with
    | zero => simp [hg, hy0]
    | succ n ih =>
      have : g (n + 1) = g n + d n := by
        simp only [hg, Finset.sum_range_succ]; abel
      rw [this, map_add (f := _), ih, hdφ]; abel
  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule R (Fin r → R))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have : g m - g n = -∑ k ∈ Finset.Ico m n, d k := by
      rw [Finset.sum_Ico_eq_sub _ hmn]; simp only [hg]; abel
    rw [this]
    refine neg_mem (Submodule.sum_mem _ fun k hk => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1) (hdmem k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' g hgc
  refine ⟨φ L, fun n => ?_⟩
  have h1 := (hL n).map φ
  rw [hgφ, ← himg n] at h1
  exact h1

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := by
  have hsm : ∀ (K : Ideal R) (x : R), x ∈ (K • (⊤ : Submodule R R)) ↔ x ∈ K := by
    intro K x
    simp [smul_eq_mul, Ideal.mul_top]
  have he' : I ^ (e + 1) ≤ J := le_trans (Ideal.pow_le_pow_right (Nat.le_succ e)) he
  have hpow : ∀ k, I ^ ((e + 1) * k) ≤ J ^ k := by
    intro k
    rw [pow_mul]
    exact Ideal.pow_right_mono he' k
  refine ⟨fun {f} hf => ?_⟩
  have hgc : ∀ {m n : ℕ}, m ≤ n →
      f ((e + 1) * m) ≡ f ((e + 1) * n) [SMOD (J ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
    rw [SModEq.sub_mem, hsm] at h ⊢
    exact hpow m h
  obtain ⟨L, hL⟩ := hJ.prec' (fun k => f ((e + 1) * k)) hgc
  refine ⟨L, fun n => ?_⟩
  have h1 := hf (show n ≤ (e + 1) * n by nlinarith)
  have h2 := hL n
  rw [SModEq.sub_mem, hsm] at h1 h2 ⊢
  have h3 : f ((e + 1) * n) - L ∈ I ^ n := Ideal.pow_right_mono hJI n h2
  have := Ideal.add_mem _ h1 h3
  simpa using this

theorem UpperTheory.V.Alg.co_finite :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'] [IsLocalRing R'],
      (∀ x : R', ∃ a : O, x - algebraMap O R' a ∈ maximalIdeal R') → IsCO O R' := by
  intro O _ _ R _ _ _ R' _ _ _ _ _ _ hres
  haveI : IsNoetherianRing R := IsCO.toIsNoetherian (O := O)
  haveI : IsNoetherian R R' := inferInstance
  haveI hN : IsNoetherianRing R' := isNoetherian_of_tower R this
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI hcompl : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hcomap : ∀ P : Ideal R', P.IsPrime → maximalIdeal R ≤ P.comap (algebraMap R R') → P = maximalIdeal R' := by
    intro P hP hle
    have hcm : (P.comap (algebraMap R R')).IsMaximal := by
      have hne : P.comap (algebraMap R R') ≠ ⊤ := (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      have : P.comap (algebraMap R R') = maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hne) hle
      rw [this]; infer_instance
    haveI := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R')
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P hcm
    exact IsLocalRing.eq_maximalIdeal this
  have hcm' : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R'))
  have hloc : IsLocalHom (algebraMap R R') := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).2 hna
    rw [← hcm', Ideal.mem_comap] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this ha
  set J : Ideal R' := (maximalIdeal R).map (algebraMap R R') with hJdef
  have hJI : J ≤ maximalIdeal R' := by
    rw [hJdef, Ideal.map_le_iff_le_comap, hcm']
  have hrad : maximalIdeal R' ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨hJP, hPp⟩ := hP
    rw [hcomap P hPp (Ideal.map_le_iff_le_comap.1 hJP)]
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal R) R' := isPrecomplete_finite (R := R) (M := R') (maximalIdeal R)
  have hJp : IsPrecomplete J R' := by
    rw [hJdef]
    exact IsPrecomplete.map_algebraMap_iff.2 this
  have hprec : IsPrecomplete (maximalIdeal R') R' := prec_cofinal hJI he hJp
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hlocO : IsLocalHom (algebraMap O R') := by
    rw [IsScalarTower.algebraMap_eq O R R']
    infer_instance
  exact
    { complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hprec }
      isLocalHom := hlocO
      res_surj := hres }
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_span_dual (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.IsTorsionBySet O M (maximalIdeal O)) (x : M) (hx : x ≠ 0) :
    ∃ D : M →ₗ[O] ResidueField O, D x ≠ 0 := by
  letI : Module (ResidueField O) M := h.module
  haveI : IsScalarTower O (ResidueField O) M := h.isScalarTower
  have := (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).not.2 hx
  push Not at this
  obtain ⟨φ, hφ⟩ := this
  exact ⟨φ.restrictScalars O, hφ⟩

theorem UpperTheory.V.Alg.co_span :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (i : B →ₐ[O] R) (S : Set R), S ⊆ maximalIdeal R →
      (∀ f f' : R →ₐ[O] DualNumber (ResidueField O), f.comp i = f'.comp i → (∀ s ∈ S, f s = f' s) → f = f') →
      maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := by
  intro O _ _ R _ _ _ B _ _ _ i S hS H x hx
  set I : Ideal R := Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 with hI
  by_contra hxI
  have hIm : I ≤ maximalIdeal R := by
    refine sup_le (sup_le (Ideal.span_le.2 hS) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_))
      (Ideal.pow_le_self two_ne_zero)
    show i b ∈ maximalIdeal R
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hb
  have hB : ∀ b ∈ maximalIdeal B, i b ∈ I := fun b hb =>
    Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb))
  have hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I := fun a ha => by
    have := hB (algebraMap O B a) (fun h => ha (IsLocalHom.map_nonunit a h))
    rwa [AlgHom.commutes] at this
  let N : Submodule O R := I.restrictScalars O ⊔ Submodule.span O {1}
  have hIN : ∀ y ∈ I, y ∈ N := fun y hy => Submodule.mem_sup_left hy
  have hON : ∀ a : O, algebraMap O R a ∈ N := fun a =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, (Algebra.algebraMap_eq_smul_one a).symm⟩)
  have hxN : N.mkQ x ≠ 0 := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Submodule.Quotient.mk_eq_zero N).1 h)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [← Algebra.algebraMap_eq_smul_one] at hyz
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hx (hIm hy)
      rwa [← hyz, add_sub_cancel_left] at this
    have h2 : a ∈ maximalIdeal O := fun h => h1 (h.map _)
    exact hxI (hyz ▸ I.add_mem hy (hO a h2))
  have htor : Module.IsTorsionBySet O (R ⧸ N) (maximalIdeal O) := by
    rintro y ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    show a • N.mkQ y = 0
    rw [← map_smul]
    refine (Submodule.Quotient.mk_eq_zero N).2 (hIN _ ?_)
    rw [Algebra.smul_def]
    exact I.mul_mem_right _ (hO a ha)
  obtain ⟨φ, hφ⟩ := co_span_dual O _ htor _ hxN
  let D : R →ₗ[O] ResidueField O := φ ∘ₗ N.mkQ
  have hD : ∀ y ∈ N, D y = 0 := fun y hy => by
    show φ (N.mkQ y) = 0
    rw [show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]
  have hres : ∀ (y : R) (a : O), y - algebraMap O R a ∈ maximalIdeal R → res O R y = algebraMap O _ a :=
    fun y a ha => by
      have := (res_eq_zero_iff O R _).2 ha
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  have hmul : ∀ y z, D (y * z) = res O R y * D z + D y * res O R z := fun y z => by
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
    obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) z
    have h1 : D ((y - algebraMap O R a) * (z - algebraMap O R b)) = 0 :=
      hD _ (hIN _ (Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)))
    have h2 : y * z = (y - algebraMap O R a) * (z - algebraMap O R b) + a • z + b • y
        - algebraMap O R (a * b) := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [h2, map_sub, map_add (f := _), map_add (f := _), h1, hD _ (hON _), map_smul, map_smul, hres y a ha, hres z b hb]
    simp only [Algebra.smul_def]; ring
  let f : R →ₐ[O] DualNumber (ResidueField O) :=
    { toFun := fun y => (res O R y, D y)
      map_one' := by
        ext
        · exact map_one (res O R)
        · exact hD _ (by simpa using hON 1)
      map_mul' := fun y z => by
        ext
        · exact map_mul (res O R) y z
        · exact hmul y z
      map_zero' := by
        ext
        · exact map_zero (res O R)
        · exact map_zero D
      map_add' := fun y z => by
        ext
        · exact map_add (res O R) y z
        · exact map_add D y z
      commutes' := fun a => by
        ext
        · exact (res O R).commutes a
        · exact hD _ (hON a) }
  let f' : R →ₐ[O] DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O R)
  have key : ∀ y, D y = 0 → f y = f' y := fun y hy => by
    ext
    · rfl
    · exact hy
  have hff : f = f' := by
    refine H f f' (AlgHom.ext fun b => key _ ?_) fun s hs => key _ (hD _ (hIN _ ?_))
    · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) b
      have := hD _ (hIN _ (hB _ ha))
      rwa [map_sub, AlgHom.commutes, map_sub, hD _ (hON a), sub_zero] at this
    · exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span hs))
  exact hφ (congrArg (fun g : R →ₐ[O] DualNumber (ResidueField O) => (g x).snd) hff)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_surj :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), maximalIdeal R' ≤ (maximalIdeal R).map f ⊔ maximalIdeal R' ^ 2 → Function.Surjective f := by
  intro O _ _ R _ _ _ R' _ _ _ f hf
  have hle : (maximalIdeal R).map f ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O R', res_map, res_eq_zero_iff]
    exact hx
  have heq : (maximalIdeal R).map (f : R →+* R') = maximalIdeal R' := by
    refine le_antisymm hle ?_
    have hfg : (maximalIdeal R').FG := IsNoetherian.noetherian _
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (maximalIdeal_le_jacobson _) ?_
    rw [smul_eq_mul, ← pow_two]
    exact hf
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := O)
  haveI : IsHausdorff ((maximalIdeal R).map (f : R →+* R')) R' := by
    rw [heq]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := maximalIdeal R) (f : R →+* R')
  intro y
  obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y0
  refine ⟨algebraMap O R a, ?_⟩
  show Ideal.Quotient.mk _ ((f : R →+* R') (algebraMap O R a)) = Ideal.Quotient.mk _ y0
  rw [Ideal.Quotient.eq, heq, AlgHom.coe_toRingHom, AlgHom.commutes, ← neg_sub]
  exact neg_mem ha
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.der_hom :
    ∀ (O A B Q : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B] [AddCommGroup Q] [Module O Q] [Module B Q] [Module Bᵐᵒᵖ Q] [IsCentralScalar B Q] [IsScalarTower O B Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] [IsScalarTower O Bᵐᵒᵖ Q] (x : A →ₐ[O] B) (D : A → Q),
      (∃ D' ∈ PtDer x Q, ⇑D' = D) ↔ ∃ y : A →ₐ[O] TrivSqZeroExt B Q, ∀ f, (y f).fst = x f ∧ (y f).snd = D f := by
  intro O A B Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ x D
  constructor
  · rintro ⟨D', hD', rfl⟩
    have hL : ∀ f g : A, D' (f * g) = x f • D' g + x g • D' f := hD'
    have h1 : D' 1 = 0 := by
      have h := hL 1 1
      simp only [mul_one, map_one, one_smul] at h
      exact left_eq_add.mp h
    refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (D' f)
              map_one' := ?_
              map_mul' := ?_
              map_zero' := ?_
              map_add' := ?_
              commutes' := ?_ }, fun f => ?_⟩
    · ext <;> simp [h1]
    · intro f g
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.fst_inr, add_zero, zero_add, op_smul_eq_smul, hL]
    · ext <;> simp
    · intro f g
      ext <;> simp [add_add_add_comm]
    · intro r
      rw [TrivSqZeroExt.algebraMap_eq_inl']
      have h0 : D' (algebraMap O A r) = 0 := by
        rw [Algebra.algebraMap_eq_smul_one, D'.map_smul, h1, smul_zero]
      ext <;> simp [h0]
    · simp
  · rintro ⟨y, hy⟩
    have hD : ∀ f, D f = (y f).snd := fun f => (hy f).2.symm
    have hX : ∀ f, x f = (y f).fst := fun f => (hy f).1.symm
    refine ⟨{ toFun := D
              map_add' := ?_
              map_smul' := ?_ }, ?_, rfl⟩
    · intro f g
      simp only [hD, map_add (f := _), TrivSqZeroExt.snd_add]
    · intro r f
      simp only [hD, map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]
    · show ∀ f g : A, _ = _
      intro f g
      show D (f * g) = x f • D g + x g • D f
      rw [hD, hD, hD, hX, hX, map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, add_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Gordan
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.gordan_dickson (σ : Type) [Finite σ] (S : Set (σ →₀ ℕ)) :
    ∃ μ : Finset (σ →₀ ℕ), (∀ m ∈ μ, m ∈ S) ∧ ∀ n ∈ S, ∃ m ∈ μ, m ≤ n := by
  classical
  haveI := Fintype.ofFinite σ
  have hfin : {m : σ →₀ ℕ | Minimal (· ∈ S) m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  refine ⟨hfin.toFinset, fun m hm => ((Set.Finite.mem_toFinset hfin).1 hm).1, fun n hn => ?_⟩
  obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hn
  exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hmin, hb⟩

theorem UpperTheory.V.Alg.gordan :
    ∀ (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X), ∃ g : Finset (σ →₀ ℕ), (∀ n ∈ g, n ≠ 0 ∧ Finsupp.weight wt n = 0) ∧
      (∀ n, Finsupp.weight wt n = 0 → n ∈ AddSubmonoid.closure (g : Set (σ →₀ ℕ))) ∧
      ∀ j, ∃ μ : Finset (σ →₀ ℕ), (∀ m ∈ μ, Finsupp.weight wt m = j) ∧ ∀ n, Finsupp.weight wt n = j → ∃ m ∈ μ, m ≤ n := by
  intro σ _ X _ _ _ wt
  classical
  obtain ⟨g, hgS, hg⟩ := gordan_dickson σ {n | n ≠ 0 ∧ Finsupp.weight wt n = 0}
  refine ⟨g, hgS, ?_, fun j => ?_⟩
  · intro n
    induction n using WellFoundedLT.induction with
    | _ n ih =>
      intro hn
      by_cases h0 : n = 0
      · rw [h0]
        exact zero_mem _
      · obtain ⟨m, hm, hmn⟩ := hg n ⟨h0, hn⟩
        have hm' := hgS m hm
        have hsplit : n = m + (n - m) := (add_tsub_cancel_of_le hmn).symm
        have hw : Finsupp.weight wt (n - m) = 0 := by
          have h1 := hn
          rw [hsplit, map_add (f := _), hm'.2, zero_add] at h1
          exact h1
        have hlt : n - m < n := by
          refine lt_of_le_of_ne tsub_le_self fun h => hm'.1 ?_
          have h2 : m + (n - m) = n := add_tsub_cancel_of_le hmn
          rw [h] at h2
          simpa using h2
        rw [hsplit]
        exact add_mem (AddSubmonoid.subset_closure hm) (ih _ hlt hw)
  · obtain ⟨μ, hμS, hμ⟩ := gordan_dickson σ {n | Finsupp.weight wt n = j}
    exact ⟨μ, hμS, hμ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.part_span :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R) (S : Set (W.σ →₀ ℕ)) (j : X), (∀ n ∈ S, Finsupp.weight W.wt n = j) →
      ∃ μ : Finset (W.σ →₀ ℕ), (μ : Set _) ⊆ S ∧ ∀ f : MvPowerSeries W.σ O, (∀ n, n ∉ S → coeff n f = 0) →
        ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, (∀ m, b m ∈ wtPart O W.wt 0) ∧ f = ∑ m ∈ μ, b m * monomial m 1 := by
  intro O R _ _ _ X _ _ _ W S j hS
  classical
  haveI := W.fin
  have hMfin : {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  have hex : ∀ n ∈ S, ∃ m ∈ {m : W.σ →₀ ℕ | Minimal (· ∈ S) m}, m ≤ n := by
    intro n hn
    obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hn
    exact ⟨b, hmin, hb⟩
  choose! c hcM hcle using hex
  refine ⟨hMfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact fun m hm => hm.1
  · intro f hf
    obtain ⟨b, hb⟩ : ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, ∀ m k,
        coeff k (b m) = if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0 :=
      ⟨fun m k => if k + m ∈ S ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
    refine ⟨b, ?_, ?_⟩
    · intro m k hk
      rw [hb, if_neg]
      rintro ⟨h1, h2⟩
      apply hk
      have hm : Finsupp.weight W.wt m = j := hS m (by rw [← h2]; exact (hcM _ h1).1)
      have hkm := hS _ h1
      rw [map_add (f := _), hm] at hkm
      simpa using hkm
    · ext n
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_congr rfl
        (g := fun m => if c n = m then (if n ∈ S then coeff n f else 0) else 0), Finset.sum_ite_eq]
      · by_cases hn : n ∈ S
        · rw [if_pos ((Set.Finite.mem_toFinset hMfin).2 (hcM n hn)), if_pos hn]
        · rw [hf n hn]
          simp
      · intro m _
        rw [MvPowerSeries.coeff_mul_monomial, mul_one]
        by_cases hmn : m ≤ n
        · rw [if_pos hmn, hb, tsub_add_cancel_of_le hmn]
          by_cases h1 : n ∈ S <;> by_cases h2 : c n = m <;> simp [h1, h2]
        · rw [if_neg hmn]
          by_cases h1 : n ∈ S
          · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
            simp [h3]
          · simp [h1]
end

