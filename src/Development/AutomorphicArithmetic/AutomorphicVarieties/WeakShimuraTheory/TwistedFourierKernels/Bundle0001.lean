module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.ClosedJ
section
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.closedJ :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) (b : R), (∀ N : ℕ, b ∈ J ⊔ maximalIdeal R ^ (N + 1)) → b ∈ J := by
  intro R _ _ _ J b hb
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J) (maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hx : Ideal.Quotient.mk J b ∈ (⨅ i : ℕ, (maximalIdeal R) ^ i • ⊤ : Submodule R (R ⧸ J)) := by
    rw [Submodule.mem_iInf]
    intro i
    rcases i with _ | N
    · simp
    · obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.mp (hb N)
      have he : Ideal.Quotient.mk J (j + y) = y • (Ideal.Quotient.mk J 1 : R ⧸ J) := by
        rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq, map_one, mul_one]
      rw [he]
      exact Submodule.smul_mem_smul hy Submodule.mem_top
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.FinQuot
section
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem pow_pow_sub_one_mem {R : Type} [CommRing R] (I : Ideal R) (l : ℕ) (hl : (l : R) ∈ I) (x : R)
    (hx : x - 1 ∈ I) (k : ℕ) : x ^ (l ^ k) - 1 ∈ I ^ (k + 1) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have h1 : x ^ (l ^ k) - 1 ∈ I := Ideal.pow_le_self (Nat.succ_ne_zero k) ih
    rw [pow_succ l k, pow_mul, ← mul_geom_sum, pow_succ I (k + 1)]
    refine Ideal.mul_mem_mul ih ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hl h1 ⊢
    rw [map_sub, map_one, sub_eq_zero] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_pow (Ideal.Quotient.mk I) (x ^ (l ^ k)), h1, one_pow]
    simpa using hl

theorem UpperTheory.V.Ws.H5.finQuot :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {R : Type} [CommRing R] [IsLocalRing R], ((l : ℕ) : R) ∈ maximalIdeal R → ∀ γ : F.G₀ →* Rˣ, TwCh F γ → ∀ N : ℕ, ∃ (Q : Type) (_ : CommGroup Q) (_ : Finite Q) (q : F.G₀ →* Q) (j : Q →* (R ⧸ maximalIdeal R ^ N)ˣ), IsPGroup l Q ∧ IsOpen (q.ker : Set F.G₀) ∧ Anti F q ∧ j.comp q = pushCh (Ideal.Quotient.mk (maximalIdeal R ^ N)) γ := by
  intro l _ F R _ _ hl γ hγ N
  haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  set χ := pushCh (Ideal.Quotient.mk (maximalIdeal R ^ N)) γ with hχ
  have hval : ∀ g, (χ g : R ⧸ maximalIdeal R ^ N) = Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R) := fun g => rfl
  have hlc : IsLocallyConstant fun g => (χ g : R ⧸ maximalIdeal R ^ N) := hγ.cont N
  have hlc' : IsLocallyConstant χ := IsLocallyConstant.desc χ Units.val hlc Units.val_injective
  have hfin : Finite χ.range := hlc'.range_finite.to_subtype
  refine ⟨χ.range, inferInstance, hfin, χ.rangeRestrict, χ.range.subtype, ?_, ?_, ?_, rfl⟩
  · rintro ⟨_, g, rfl⟩
    refine ⟨N, Subtype.ext (Units.ext ?_)⟩
    have h := Ideal.pow_le_pow_right (Nat.le_succ N) (pow_pow_sub_one_mem _ l hl _ (hγ.red g) N)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, map_pow] at h
    simpa [hval] using h
  · rw [MonoidHom.ker_rangeRestrict]
    exact hlc'.isOpen_fiber 1
  · refine hγ.toAnti.mono fun g hg => ?_
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hg
    exact Units.ext (by rw [hval, hg]; simp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.Fourier
section
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.fourier :
    ∀ (K Q : Type) [Field K] [IsAlgClosed K] [CharZero K] [CommGroup Q] [Finite Q] (a : MonoidAlgebra K Q), (∀ χ : Q →* Kˣ, MonoidAlgebra.lift K K Q ((Units.coeHom K).comp χ) a = 0) → a = 0 := by
  intro K Q _ _ _ _ _ a h
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : NeZero (Monoid.exponent Q) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent Q : ℕ) : K) := ⟨by exact_mod_cast NeZero.ne (Monoid.exponent Q)⟩
  let ev : Q → ((Q →* Kˣ) →* K) := fun q =>
    { toFun := fun χ => (χ q : K), map_one' := by simp, map_mul' := fun x y => by simp }
  have hinj : Function.Injective ev := by
    intro q q' hq
    refine (CommGroup.forall_apply_eq_apply_iff Q (M := K)).1 fun φ => ?_
    exact Units.ext (DFunLike.congr_fun hq φ)
  have hli := (linearIndependent_monoidHom (Q →* Kˣ) K).comp ev hinj
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun q => a.coeff q) (by
    funext χ
    have := h χ
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [ev, Finset.sum_apply] using this)
  ext q
  simpa using key q
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LamSmul
section
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem coeff_chi_smul {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (a : A)
    (y : MonoidAlgebra A G) (i : ℕ) (hi : i ≤ n) :
    (D.chi (a • y)).coeff (n - i) = (-a) ^ i * D.lam i y := by
  have hsum : D.chi (a • y) = ∑ j ∈ Finset.range (n + 1), C (D.lam j y * (-a) ^ j) * X ^ (n - j) := by
    have h := AlgebraTools.Det.expand D y A[X] X (C (-a))
    rw [Polynomial.algebraMap_eq] at h
    unfold GDet.chi
    have harg : MonoidAlgebra.single 1 X - (MonoidAlgebra.mapRingHom G C) (a • y) =
        MonoidAlgebra.single 1 X + C (-a) • (MonoidAlgebra.mapRingHom G C) y := by
      rw [map_neg, neg_smul, ← sub_eq_add_neg]
      congr 1
      ext g
      simp [MonoidAlgebra.mapRingHom]
    rw [harg, h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow]
    ring
  rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    ring
  · intro j hj hji
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h
    apply hji
    have := Finset.mem_range.mp hj
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem UpperTheory.V.Ws.H5.lamSmul :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (a : A) (y : MonoidAlgebra A G) (i : ℕ), D.lam i (a • y) = a ^ min i n * D.lam i y := by
  intro n A G _ _ D a y i
  have hl : ∀ (z : MonoidAlgebra A G) (j : ℕ), D.lam j z = (-1) ^ j * (D.chi z).coeff (n - j) := by
    intro z j
    unfold GDet.lam
    rfl
  rcases le_or_gt i n with hi | hi
  · rw [hl, coeff_chi_smul D a y i hi, min_eq_left hi, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  · have hn : n - i = n - n := by omega
    have h1 := coeff_chi_smul D 1 y n le_rfl
    rw [one_smul] at h1
    rw [hl (a • y), hl y, hn, coeff_chi_smul D a y n le_rfl, h1, min_eq_right hi.le, neg_pow a n]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.SingleSubMem
section
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem comap_max {B Q : Type} [CommRing B] [IsLocalRing B] [CommGroup Q] [Finite Q]
    (M : Ideal (MonoidAlgebra B Q)) [M.IsMaximal] :
    M.comap (algebraMap B (MonoidAlgebra B Q)) = maximalIdeal B :=
  eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) M)

private theorem single_sub_mem {l : ℕ} (hl : l.Prime) {B Q : Type} [CommRing B] [IsLocalRing B]
    [CommGroup Q] [Finite Q] (hB : ((l : ℕ) : B) ∈ maximalIdeal B) (hQ : IsPGroup l Q)
    (M : Ideal (MonoidAlgebra B Q)) [hM : M.IsMaximal] (z : Q) :
    (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ M := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨k, hk⟩ := hQ z
  have hlM : ((l : ℕ) : MonoidAlgebra B Q) ∈ M := by
    have h1 : ((l : ℕ) : B) ∈ M.comap (algebraMap B (MonoidAlgebra B Q)) := by
      rw [comap_max M]
      exact hB
    rw [Ideal.mem_comap, map_natCast] at h1
    exact h1
  letI : Field (MonoidAlgebra B Q ⧸ M) := Ideal.Quotient.field M
  have hlK : ((l : ℕ) : MonoidAlgebra B Q ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    exact hlM
  haveI : CharP (MonoidAlgebra B Q ⧸ M) l := by
    rcases hl.eq_one_or_self_of_dvd _ (ringChar.dvd hlK) with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one)
    · rw [← h1]
      exact ringChar.charP _
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : (Ideal.Quotient.mk M (MonoidAlgebra.single z 1 - 1)) ^ l ^ k = 0 := by
    rw [map_sub, map_one, sub_pow_char_pow, one_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hk,
      ← MonoidAlgebra.one_def, map_one, sub_self]
  exact (pow_eq_zero_iff (pow_ne_zero k hl.ne_zero)).mp h0

private theorem sub_aug_mem {B Q : Type} [CommRing B] [CommGroup Q]
    (M : Ideal (MonoidAlgebra B Q))
    (h : ∀ z : Q, (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ M) (x : MonoidAlgebra B Q) :
    x - algebraMap B (MonoidAlgebra B Q) (MonoidAlgebra.lift B B Q 1 x) ∈ M := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact M.add_mem hx hy
  | single g b =>
    have e : MonoidAlgebra.single g b - algebraMap B (MonoidAlgebra B Q) (MonoidAlgebra.lift B B Q 1 (MonoidAlgebra.single g b)) =
        algebraMap B (MonoidAlgebra B Q) b * (MonoidAlgebra.single g 1 - 1) := by
      rw [MonoidAlgebra.lift_single]
      simp [mul_sub, MonoidAlgebra.single_mul_single, MonoidAlgebra.one_def]
    rw [e]
    exact M.mul_mem_left _ (h g)

theorem UpperTheory.V.Ws.H5.grpCO :
    ∀ (l : ℕ) [Fact l.Prime] (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B], ((l : ℕ) : B) ∈ maximalIdeal B → ∀ (Q : Type) [CommGroup Q] [Finite Q], IsPGroup l Q → ∃ _ : IsCO O (MonoidAlgebra B Q), ∀ z : Q, (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ maximalIdeal (MonoidAlgebra B Q) := by
  intro l _ O B _ _ _ _ _ hB Q _ _ hQ
  have hl : l.Prime := Fact.out
  let aug : MonoidAlgebra B Q →+* B := (MonoidAlgebra.lift B B Q 1).toRingHom
  let φ : MonoidAlgebra B Q →+* ResidueField B := (residue B).comp aug
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    refine ⟨algebraMap B _ b, ?_⟩
    simp [φ, aug]
  have hM0 := RingHom.ker_isMaximal_of_surjective φ hφ
  have hle : ∀ (M : Ideal (MonoidAlgebra B Q)), M.IsMaximal → RingHom.ker φ ≤ M := by
    intro M hM x hx
    have h1 : aug x ∈ maximalIdeal B := by
      rw [RingHom.mem_ker] at hx
      exact (residue_eq_zero_iff _).mp hx
    have h2 : algebraMap B _ (aug x) ∈ M := by
      have : aug x ∈ M.comap (algebraMap B _) := by
        rw [comap_max M]
        exact h1
      exact this
    have h3 : x - algebraMap B _ (aug x) ∈ M := sub_aug_mem M (single_sub_mem hl hB hQ M) x
    have := M.add_mem h3 h2
    rwa [sub_add_cancel] at this
  haveI : IsLocalRing (MonoidAlgebra B Q) := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨RingHom.ker φ, hM0, fun M hM => ?_⟩
    exact (hM0.eq_of_le hM.ne_top (hle M hM)).symm
  have hres : ∀ x : MonoidAlgebra B Q, ∃ a : O, x - algebraMap O _ a ∈ maximalIdeal (MonoidAlgebra B Q) := by
    intro x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (aug x)
    refine ⟨a, ?_⟩
    have h3 : x - algebraMap B _ (aug x) ∈ maximalIdeal (MonoidAlgebra B Q) :=
      sub_aug_mem _ (single_sub_mem hl hB hQ _) x
    have h4 : algebraMap B (MonoidAlgebra B Q) (aug x - algebraMap O B a) ∈ maximalIdeal (MonoidAlgebra B Q) := by
      have : aug x - algebraMap O B a ∈ (maximalIdeal (MonoidAlgebra B Q)).comap (algebraMap B _) := by
        rw [comap_max]
        exact ha
      exact this
    have := (maximalIdeal _).add_mem h3 h4
    rw [IsScalarTower.algebraMap_apply O B (MonoidAlgebra B Q)]
    rwa [map_sub, sub_add_sub_cancel] at this
  exact ⟨co_finite O B (MonoidAlgebra B Q) hres, fun z => single_sub_mem hl hB hQ _ z⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwChOps
section
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.twChOps :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {R : Type} [CommRing R] [IsLocalRing R] (γ : F.G₀ →* Rˣ), TwCh F γ → (∀ m : ℕ, TwCh F (γ ^ m)) ∧ TwCh F γ⁻¹ ∧ ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (e : R →+* R'), IsLocalHom e → TwCh F (pushCh e γ) := by
  intro l _ F R _ _ γ hγ
  have hq : ∀ g, Ideal.Quotient.mk (maximalIdeal R) (γ g : R) = 1 := fun g => by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hγ.red g
  refine ⟨fun m => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩, ⟨hγ.toAnti.mono ?_, ?_, ?_⟩,
    fun R' _ _ e he => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩⟩
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  · intro N
    have hc := (hγ.cont N).comp (fun x => x ^ m)
    convert hc using 1
    funext g
    simp [Function.comp]
  · intro g
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    simp [hq g]
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  · intro N
    have hc := (hγ.cont N).comp Ring.inverse
    convert hc using 1
    funext g
    have hu : Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R) =
        ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N) : R →* R ⧸ maximalIdeal R ^ N) (γ g) : _)) := rfl
    simp only [Function.comp_apply]
    rw [hu, Ring.inverse_unit, Units.coe_map_inv]
    rfl
  · intro g
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    have h2 := congrArg (Ideal.Quotient.mk (maximalIdeal R)) (γ g).inv_mul
    rw [map_mul, hq g, mul_one, map_one] at h2
    simpa using h2
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [pushCh, hg]
  · intro N
    have hle : maximalIdeal R ^ N ≤ Ideal.comap e (maximalIdeal R' ^ N) := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr (fun x hx => Ideal.mem_comap.mpr (map_nonunit e x hx))) N
    have hc := (hγ.cont N).comp (Ideal.quotientMap _ e hle)
    convert hc using 1
    funext g
    simp [pushCh, Ideal.quotientMap_mk]
  · intro g
    have h3 := map_nonunit e _ (hγ.red g)
    simpa [pushCh] using h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwMapUniq
section
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.twMapUniq :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f₀ : B.B →+* R) (γ : F.G₀ →* Rˣ) (f f' : B.B →ₐ[O] R), TwMap B f₀ (f : B.B →+* R) γ → TwMap B f₀ (f' : B.B →+* R) γ → f = f' := by
  intro l _ F O _ _ _ n r B R _ _ _ f₀ γ f f' hf hf'
  obtain ⟨p, hp⟩ := exists_determinantPair_map_of_algHom l F O n r B.B R f B.u
  have hs : ∀ (φ : B.B →+* R) (g : F.G₀), MonoidAlgebra.mapRingHom F.G₀ φ (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    intro φ g
    simp [MonoidAlgebra.mapRingHom]
  have hD : B.u.D.map (f' : B.B →+* R) = B.u.D.map (f : B.B →+* R) := by
    apply CA.d_gext
    intro g i _ hi
    have e1 := ((CA.d_gmap B.u.D).2.2.1 (f : B.B →+* R) (MonoidAlgebra.single g 1)).2 i
    have e2 := ((CA.d_gmap B.u.D).2.2.1 (f' : B.B →+* R) (MonoidAlgebra.single g 1)).2 i
    rw [hs] at e1 e2
    rw [e1, e2, hf.1 g i hi, hf'.1 g i hi]
  have hψ : ∀ v i, pushCh (f' : B.B →+* R) (B.u.ψ v i) = pushCh (f : B.B →+* R) (B.u.ψ v i) := by
    intro v i
    ext g
    simp only [pushCh, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    exact (hf'.2 v i g).trans (hf.2 v i g).symm
  have hp' : B.u.Maps (f' : B.B →+* R) p.D p.ψ := by
    unfold Pair.Maps at hp ⊢
    exact ⟨hD.trans hp.1, fun v i => (hψ v i).trans (hp.2 v i)⟩
  obtain ⟨h, _, huniq⟩ := B.univ R p
  exact (huniq f hp).trans (huniq f' hp').symm
end

