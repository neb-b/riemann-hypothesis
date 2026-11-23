module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CmplPt
section
open IsLocalRing UpperTheory.V.Alg

private theorem mem_pow_iff {A : Type} [CommRing A] (I : Ideal A) (fg : I.FG) (n : ℕ) (y : AdicCompletion I A) :
    y ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) ↔ AdicCompletion.eval I A n y = 0 := by
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg]
  rfl

private theorem dense {A : Type} [CommRing A] (I : Ideal A) (fg : I.FG) (n : ℕ) (y : AdicCompletion I A) :
    ∃ z : A, y - algebraMap A (AdicCompletion I A) z ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I A n y)
  refine ⟨z, ?_⟩
  rw [mem_pow_iff I fg]
  change AdicCompletion.eval I A n (y - AdicCompletion.of I A z) = 0
  rw [map_sub, AdicCompletion.eval_of, Submodule.mkQ_apply, hz, sub_self]

private theorem lift_ex {A R : Type} [CommRing A] [CommRing R] (I : Ideal A) (J : Ideal R) [IsAdicComplete J R]
    (g : A →+* R) (hg : I ≤ J.comap g) :
    ∃ h : AdicCompletion I A →+* R, ∀ z, h (algebraMap A _ z) = g z := by
  have hle : ∀ n, I ^ n ≤ (J ^ n).comap g := fun n => (Ideal.pow_right_mono hg n).trans (Ideal.le_comap_pow _ n)
  refine ⟨IsAdicComplete.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) g (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n))
    (fun {m n} hmn => RingHom.ext fun y => ?_), fun z => ?_⟩
  · induction y using AdicCompletion.induction_on with | _ s => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]
    exact congrArg (Ideal.quotientMap (J ^ m) g (hle m)) (AdicCompletion.Ideal.mk_eq_mk I hmn s)
  · refine IsHausdorff.eq_iff_smodEq (I := J) |>.2 fun n => ?_
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom]
    show Ideal.quotientMap (J ^ n) g (hle n) (AdicCompletion.evalₐ I n (AdicCompletion.of I A z)) = _
    rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

theorem UpperTheory.V.Ws.cmplPt {Λ A : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing A] [Algebra Λ A] [IsNoetherianRing A]
    (x : A →ₐ[Λ] ResidueField Λ) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (f : A →ₐ[Λ] R),
      (f : A →+* R).Flat ∧ (res Λ R).comp f = x ∧
      ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (g : A →ₐ[Λ] R'), (res Λ R').comp g = x →
        ∃! h : R →ₐ[Λ] R', h.comp f = g := by
  have hx : ∀ z : A, ∃ c : Λ, z - algebraMap Λ A c ∈ RingHom.ker x := fun z => by
    obtain ⟨c, hc⟩ := residue_surjective (x z)
    exact ⟨c, by rw [RingHom.mem_ker, map_sub, AlgHom.commutes, ← hc]; exact sub_self _⟩
  have hs : Function.Surjective x := fun y => by
    obtain ⟨c, rfl⟩ := residue_surjective y
    exact ⟨algebraMap Λ A c, x.commutes c⟩
  set I : Ideal A := RingHom.ker x with hI
  haveI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective x hs
  have fg : I.FG := I.fg_of_isNoetherianRing
  let R := AdicCompletion I A
  haveI hmax := AdicCompletion.isMaximal_map_of_le I I le_rfl fg
  haveI hc := AdicCompletion.isAdicComplete_self I fg
  haveI : IsLocalRing R := isLocalRing_of_isAdicComplete_maximal (I.map (algebraMap A R))
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm : maximalIdeal R = I.map (algebraMap A R) := (eq_maximalIdeal hmax).symm
  let f : A →ₐ[Λ] R := IsScalarTower.toAlgHom Λ A R
  have hf : ∀ z, f z = algebraMap A R z := fun _ => rfl
  have hIm : ∀ z ∈ I, f z ∈ maximalIdeal R := fun z hz => hm ▸ Ideal.mem_map_of_mem _ hz
  haveI hco : IsCO Λ R :=
    { complete := hm ▸ hc
      isLocalHom := ⟨fun c hu => by
        by_contra hn
        have h0 : algebraMap Λ A c ∈ I := by
          rw [RingHom.mem_ker, AlgHom.commutes]
          exact (residue_eq_zero_iff c).2 hn
        have h1 := hIm _ h0
        rw [AlgHom.commutes] at h1
        exact h1 hu⟩
      res_surj := fun y => by
        obtain ⟨z, hz⟩ := dense I fg 1 y
        obtain ⟨c, hc⟩ := hx z
        refine ⟨c, ?_⟩
        rw [pow_one, ← hm, ← hf] at hz
        have h1 := add_mem hz (hIm _ hc)
        rwa [map_sub, AlgHom.commutes, sub_add_sub_cancel] at h1 }
  refine ⟨R, inferInstance, inferInstance, hco, f,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I), AlgHom.ext fun z => ?_, fun R' _ _ _ g hg => ?_⟩
  · obtain ⟨c, hc⟩ := hx z
    have h1 := (res_eq_zero_iff Λ R _).2 (hIm _ hc)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hc
    rw [map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    exact h1.trans hc.symm
  · have hgI : I ≤ (maximalIdeal R').comap (g : A →+* R') := fun z hz =>
      (res_eq_zero_iff Λ R' _).1 ((AlgHom.congr_fun hg z).trans hz)
    obtain ⟨h, hh⟩ := lift_ex I (maximalIdeal R') (g : A →+* R') hgI
    have uniq : ∀ h₁ h₂ : R →ₐ[Λ] R', h₁.comp f = g → h₂.comp f = g → h₁ = h₂ := fun h₁ h₂ e₁ e₂ => by
      refine AlgHom.ext fun y => IsHausdorff.eq_iff_smodEq (I := maximalIdeal R') |>.2 fun n => ?_
      obtain ⟨z, hz⟩ := dense I fg n y
      have k : ∀ φ : R →ₐ[Λ] R', φ.comp f = g → φ y - g z ∈ maximalIdeal R' ^ n := fun φ e => by
        have hle : (I ^ n).map (algebraMap A R) ≤ (maximalIdeal R' ^ n).comap (φ : R →+* R') := by
          rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
          have e' : (φ : R →+* R').comp (algebraMap A R) = (g : A →+* R') := RingHom.ext fun w => AlgHom.congr_fun e w
          rw [e']
          exact (Ideal.pow_right_mono hgI n).trans (Ideal.le_comap_pow _ n)
        have h1 : φ (y - f z) ∈ maximalIdeal R' ^ n := hle hz
        rwa [map_sub, ← AlgHom.comp_apply φ f, e] at h1
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      simpa using sub_mem (k h₁ e₁) (k h₂ e₂)
    let h' : R →ₐ[Λ] R' := { h with commutes' := fun c => (hh (algebraMap Λ A c)).trans (g.commutes c) }
    have e : h'.comp f = g := AlgHom.ext hh
    exact ⟨h', e, fun h₁ e₁ => uniq _ _ e₁ e⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedDual
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section
variable {R : Type} [CommRing R]

private theorem rd_adj_mul (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem rd_adj_one : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

private theorem rd_sp {n n' m : M4 R} (h1 : n * m = 1) (h : adj n' * n + adj n * n' = 0) : n' * m ∈ sp4 R := by
  show adj _ = -_
  have e : adj n' = -(adj n * (n' * m)) := by
    have := congrArg (· * m) h
    simp only [add_mul, mul_assoc, h1, mul_one, zero_mul] at this
    exact eq_neg_of_add_eq_zero_left this
  rw [rd_adj_mul, e, mul_neg, ← mul_assoc, ← rd_adj_mul, h1, rd_adj_one, one_mul]

private theorem rd_up_mul {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l < i
  · rw [hX i l hl, zero_mul]
  · rw [hY l j (lt_of_lt_of_le hij (not_lt.1 hl)), mul_zero]

end

section
variable {k : Type} [Field k]

private theorem rd_snd_mul (X Y : M4 (DualNumber k)) :
    (X * Y).map TrivSqZeroExt.snd = X.map TrivSqZeroExt.snd * Y.map TrivSqZeroExt.fst
      + X.map TrivSqZeroExt.fst * Y.map TrivSqZeroExt.snd := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four, TrivSqZeroExt.snd_add,
    DualNumber.snd_mul]
  ring

private theorem rd_fst_mul (X Y : M4 (DualNumber k)) :
    (X * Y).map TrivSqZeroExt.fst = X.map TrivSqZeroExt.fst * Y.map TrivSqZeroExt.fst := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_four, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul]

private theorem rd_snd_adj (X : M4 (DualNumber k)) : (adj X).map TrivSqZeroExt.snd = adj (X.map TrivSqZeroExt.snd) := by
  ext i j
  simp only [adj_apply, Matrix.map_apply, TrivSqZeroExt.snd_smul]

private theorem rd_fst_adj (X : M4 (DualNumber k)) : (adj X).map TrivSqZeroExt.fst = adj (X.map TrivSqZeroExt.fst) := by
  ext i j
  simp only [adj_apply, Matrix.map_apply, TrivSqZeroExt.fst_smul]

private theorem rd_gsp {ν : DualNumber k} (hν : ν.snd = 0) {X : M4 (DualNumber k)} (h : IsGSp ν X) :
    adj (X.map TrivSqZeroExt.snd) * X.map TrivSqZeroExt.fst + adj (X.map TrivSqZeroExt.fst) * X.map TrivSqZeroExt.snd = 0 := by
  rw [← rd_snd_adj, ← rd_fst_adj, ← rd_snd_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij, hν]

private theorem rd_gsp_one {X : M4 (DualNumber k)} (h : IsGSp 1 X) :
    adj (X.map TrivSqZeroExt.fst) * X.map TrivSqZeroExt.fst = 1 := by
  rw [← rd_fst_adj, ← rd_fst_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.redDual :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* DualNumber k) (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ k) (Q : PD Φ.ι Γ (DualNumber k)),
          (∀ x, (a x).snd = 0) → Φ.IsPair a Q → (∀ i j, IsLocallyConstant fun g => Q.r g i j) → (∀ g i j, (Q.r g i j).fst = c.r g i j) → (∀ v i j, (Q.n v i j).fst = c.n v i j) → Supp S Q.r →
          ((fun g => (Q.r g).map TrivSqZeroExt.snd * c.r g⁻¹, fun v => (Q.n v).map TrivSqZeroExt.snd * adj (c.n v)) : (Γ → M4 k) × (Φ.ι → M4 k)) ∈ Φ.Tan S c := by
  intro O Γ _ _ _ _ Φ k _ a S c Q ha hP hlc hr hn hS
  have er : ∀ g, (Q.r g).map TrivSqZeroExt.fst = c.r g := fun g => Matrix.ext (hr g)
  have en : ∀ v, (Q.n v).map TrivSqZeroExt.fst = c.n v := fun v => Matrix.ext (hn v)
  have i1 : ∀ g, c.r g * c.r g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have i2 : ∀ g, c.r g⁻¹ * c.r g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have n1 : ∀ v, adj (c.n v) * c.n v = 1 := fun v => en v ▸ rd_gsp_one (hP.low v).1
  have n2 : ∀ v, c.n v * adj (c.n v) = 1 := fun v => mul_eq_one_comm.1 (n1 v)
  have n3 : ∀ v, adj ((Q.n v).map TrivSqZeroExt.snd) * c.n v + adj (c.n v) * (Q.n v).map TrivSqZeroExt.snd = 0 :=
    fun v => en v ▸ rd_gsp rfl (hP.low v).1
  have hl : IsLocallyConstant fun g => Q.r g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have : ∀ᶠ y in nhds x, ∀ i j, Q.r y i j = Q.r x i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hlc i j).eventually_eq x
    exact this.mono fun y hy => Matrix.ext hy
  refine ⟨?_, fun g => ?_, fun g h => ?_, fun g hg => ?_, ?_, fun g i j hij hw => ?_, fun v => ⟨rd_sp (n2 v) (n3 v), fun i j hij => ?_⟩,
    fun v s hs => ?_⟩
  · have h1 := hl.comp fun X : M4 (DualNumber k) => X.map TrivSqZeroExt.snd
    have h2 := (hl.comp fun X : M4 (DualNumber k) => X.map TrivSqZeroExt.fst).comp_continuous continuous_inv
    have h3 := h1.mul h2
    convert h3 using 1
    funext g
    simp only [Function.comp_apply, Pi.mul_apply, er]
  · exact rd_sp (i1 g) (er g ▸ rd_gsp (ha _) (hP.mult g))
  · show _ * _ = _ * _ + _ * (_ * _) * _
    rw [map_mul, rd_snd_mul, er, er, mul_inv_rev, map_mul, add_mul, mul_assoc, ← mul_assoc (c.r h), i1, one_mul]
    simp only [mul_assoc]
  · show _ * _ = _
    rw [hP.kill g hg]
    have : (1 : M4 (DualNumber k)).map TrivSqZeroExt.snd = 0 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [this, zero_mul]
  · have d1 : ((Q.r Φ.g0).map TrivSqZeroExt.snd).IsDiag := hP.nrm.map rfl
    have d2 : (c.r Φ.g0).IsDiag := er _ ▸ hP.nrm.map rfl
    intro i j hij
    have e := i1 Φ.g0
    rw [← d2.diagonal_diag] at e
    have e1 := congrFun (congrFun e i) i
    have e2 := congrFun (congrFun e i) j
    rw [Matrix.diagonal_mul, Matrix.one_apply_eq] at e1
    rw [Matrix.diagonal_mul, Matrix.one_apply_ne hij] at e2
    have e3 := (mul_eq_zero.1 e2).resolve_left (left_ne_zero_of_mul_eq_one e1)
    show (_ * _ : M4 k) i j = 0
    rw [← d1.diagonal_diag, Matrix.diagonal_mul, e3, mul_zero]
  · show (_ * _ * _ : M4 k) i j = 0
    rw [mul_assoc, i2, mul_one, Matrix.map_apply, hS g i j hij hw]
    rfl
  · show (_ * (_ * _) * _ : M4 k) i j = 0
    rw [mul_assoc, mul_assoc, n1, mul_one, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : i < l
    · rw [adj_apply, ← hn, (hP.low v).2.2 _ _ (Fin.rev_lt_rev.2 hl)]
      simp
    · rw [Matrix.map_apply]
      rcases ((not_lt.1 hl).trans hij).lt_or_eq with h | h
      · rw [(hP.low v).2.2 _ _ h]; simp
      · rw [h, (hP.low v).2.1]; simp
  · have u1 : IsUp ((adj (Q.n v) * Q.r s * Q.n v).map TrivSqZeroExt.snd) := fun i j hij => by
      rw [Matrix.map_apply, hP.flag v s hs i j hij]; rfl
    have u2 : IsUp ((adj (Q.n v) * Q.r s⁻¹ * Q.n v).map TrivSqZeroExt.fst) := fun i j hij => by
      rw [Matrix.map_apply, hP.flag v _ (inv_mem hs) i j hij]; rfl
    have u := rd_up_mul u1 u2
    simp only [rd_snd_mul, rd_fst_mul, rd_snd_adj, rd_fst_adj, er, en] at u
    convert u using 1
    have k1 : ∀ X : M4 k, c.n v * (adj (c.n v) * X) = X := fun X => by rw [← mul_assoc, n2, one_mul]
    have k2 : ∀ X : M4 k, c.r s * (c.r s⁻¹ * X) = X := fun X => by rw [← mul_assoc, i1, one_mul]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, k1, k2, n1, mul_one, eq_neg_of_add_eq_zero_left (n3 v)]
    abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedTanFlow
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

theorem rank_le_of_lowest : ∀ {k V : Type} [Field k] [AddCommGroup V] [Module k V] (π : ℤ → V →ₗ[k] V) (T U : Submodule k V),
      (∀ p q x, π p (π q x) = if p = q then π q x else 0) → (∃ lo : ℤ, ∀ q < lo, π q = 0) →
      (∃ hi : ℤ, ∀ x, (∀ q < hi, π q x = 0) → x = 0) →
      (∀ p, ∀ x ∈ T, (∀ q < p, π q x = 0) → π p x ∈ U) → Module.rank k T ≤ Module.rank k U := by
  intro k V _ _ _ π T U h ⟨lo, hlo⟩ ⟨hi, hhi⟩ H
  let K : ℤ → Submodule k V := fun p => ⨅ q < p, LinearMap.ker (π q)
  have hK : ∀ p x, x ∈ K p ↔ ∀ q < p, π q x = 0 := fun p x => by simp [K, Submodule.mem_iInf]
  have step : ∀ (W : Submodule k V) p, Module.rank k ↥(W ⊓ K p) =
      Module.rank k ↥((W ⊓ K p).map (π p)) + Module.rank k ↥(W ⊓ K (p + 1)) := by
    intro W p
    rw [← LinearMap.rank_range_add_rank_ker ((π p).domRestrict (W ⊓ K p)), LinearMap.range_domRestrict]
    congr 1
    rw [LinearMap.ker_domRestrict]
    have e : W ⊓ K (p + 1) = (W ⊓ K p) ⊓ LinearMap.ker (π p) := by
      ext x
      simp only [Submodule.mem_inf, hK, LinearMap.mem_ker]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun q hq => h2 q (by omega)⟩, h2 p (by omega)⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun q hq => ?_⟩
        rcases lt_or_eq_of_le (show q ≤ p by omega) with h4 | rfl
        exacts [h2 q h4, h3]
    rw [e, ← Submodule.map_comap_subtype (W ⊓ K p) (LinearMap.ker (π p))]
    exact (Submodule.equivMapOfInjective _ (W ⊓ K p).subtype_injective _).rank_eq
  have main : ∀ p ≤ max hi lo, Module.rank k ↥(T ⊓ K p) ≤ Module.rank k ↥(U ⊓ K p) := by
    intro p hp
    induction p using Int.inductionOn' (b := max hi lo) with
    | zero =>
      have : T ⊓ K (max hi lo) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact hhi x fun q hq => (hK _ _).1 hx.2 q (lt_max_of_lt_left hq)
      rw [this]; simp
    | succ n hn ih => omega
    | pred n hn ih =>
      rw [step T, step U, sub_add_cancel]
      refine add_le_add (Submodule.rank_mono ?_) (ih hn)
      rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
      refine ⟨π (n - 1) x, ⟨H _ x h1 ((hK _ _).1 h2), (hK _ _).2 fun q hq => ?_⟩, ?_⟩
      · rw [h, if_neg hq.ne]
      · rw [h, if_pos rfl]
  have top : K lo = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (hK _ _).2 fun q hq => by simp [hlo q hq]
  have := main lo (le_max_right _ _)
  rwa [top, inf_top_eq, inf_top_eq] at this

theorem tan_lowest : ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (S : Finset (ℤ × ℤ)) (c c₀ : PD Φ.ι Γ k) (m : Fin 4 → ℤ), Symp m →
      (∀ g, Lim m (c.r g) (c₀.r g)) → (∀ v, Lim m (c.n v) (c₀.n v)) → ∀ p : ℤ, ∀ x ∈ Φ.Tan S c,
      (∀ g, FGe m p (x.1 g)) → (∀ v, FGe m p (x.2 v)) → Φ.cmpT m p x ∈ Φ.Tan S c₀ := by
  intro O Γ _ _ _ Φ k _ S c c₀ m hm hr hn p x ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ hX hY
  have c3 : ∀ {A B Z : M4 k}, FGe m 0 A → FGe m 0 B → FGe m p Z →
      FGe m p (A * Z * B) ∧ cmp m p (A * Z * B) = cmp m 0 A * cmp m p Z * cmp m 0 B := by
    intro A B Z hA hB hZ
    have h1 := (hA.mul hZ).mul hB
    have h2 := cmp_mul (hA.mul hZ) hB
    rw [cmp_mul hA hZ] at h2
    simp only [zero_add, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  have csp : ∀ {Z : M4 k}, Z ∈ sp4 k → cmp m p Z ∈ sp4 k := by
    intro Z hZ
    show adj _ = -_
    rw [← cmp_adj hm, show adj Z = -Z from hZ, map_neg]
  have cz : ∀ {Z : M4 k} {i j}, Z i j = 0 → cmp m p Z i j = 0 := by
    intro Z i j h
    simp [cmp_apply, h]
  have cn : ∀ v {Z : M4 k}, FGe m p Z → adj (c₀.n v) * cmp m p Z * c₀.n v = cmp m p (adj (c.n v) * Z * c.n v) := by
    intro v Z hZ
    rw [(c3 ((hn v).1.adj hm) (hn v).1 hZ).2, cmp_adj hm, ← (hn v).2]
  refine ⟨a1.comp (cmp m p), fun g => csp (a2 g), fun g h => ?_, fun g h => ?_, fun i j h => cz (a5 h),
    fun g i j h1 h2 => ?_, fun v => ⟨csp (a7 v).1, fun i j h => ?_⟩, fun v s hs i j h => ?_⟩
  · simp only [Fr.cmpT_fst]
    rw [a3, map_add (f := _), (c3 (hr g).1 (hr g⁻¹).1 (hX h)).2, ← (hr g).2, ← (hr g⁻¹).2]
  · rw [Fr.cmpT_fst, a4 g h, map_zero]
  · have := cmp_mul (hX g) (hr g).1
    rw [add_zero, ← (hr g).2] at this
    rw [Fr.cmpT_fst, ← this]
    exact cz (a6 g i j h1 h2)
  · rw [Fr.cmpT_snd, cn v (hY v)]
    exact cz ((a7 v).2 i j h)
  · have h3 := c3 (hr s).1 (hr s⁻¹).1 (hY v)
    rw [← (hr s).2, ← (hr s⁻¹).2] at h3
    rw [Fr.cmpT_snd, Fr.cmpT_fst, ← h3.2, ← map_add (f := _), ← map_sub, cn v (((hX s).add h3.1).sub (hY v))]
    exact cz (a8 v s hs i j h)

theorem tan_flow {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k]
    (S : Finset (ℤ × ℤ)) (c c₀ : PD Φ.ι Γ k) (m : Fin 4 → ℤ) (hm : Symp m)
    (hr : ∀ g, Lim m (c.r g) (c₀.r g)) (hn : ∀ v, Lim m (c.n v) (c₀.n v)) :
    Module.rank k (Φ.TanS S c) ≤ Module.rank k (Φ.TanS S c₀) := by
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ i j, |m i - m j| < N :=
    ⟨∑ z : Fin 4 × Fin 4, |m z.1 - m z.2| + 1, fun i j => Int.lt_add_one_of_le
      (Finset.single_le_sum (f := fun z : Fin 4 × Fin 4 => |m z.1 - m z.2|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (i, j)))⟩
  have ge : ∀ {p : ℤ} {Z : M4 k}, (∀ q < p, cmp m q Z = 0) → FGe m p Z := by
    intro p Z h i j hij
    have := congrFun (congrFun (h _ hij) i) j
    simpa [cmp_apply] using this
  have cc : ∀ (p q : ℤ) (Z : M4 k), cmp m p (cmp m q Z) = if p = q then cmp m q Z else 0 := by
    intro p q Z
    ext i j
    by_cases h : p = q
    · subst h; simp only [cmp_apply, if_true]; split_ifs <;> rfl
    · simp only [cmp_apply, if_neg h, Matrix.zero_apply]
      split_ifs with h1 h2
      · omega
      all_goals rfl
  refine rank_le_of_lowest (Φ.cmpT m) _ _ (fun p q x => ?_) ⟨-N, fun q hq => ?_⟩ ⟨N, fun x hx => ?_⟩ fun p x hx h => ?_
  · refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
    · rw [Fr.cmpT_fst, Fr.cmpT_fst, cc]; split_ifs <;> rfl
    · rw [Fr.cmpT_snd, Fr.cmpT_snd, cc]; split_ifs <;> rfl
  · have : ∀ Z : M4 k, cmp m q Z = 0 := fun Z => by
      ext i j
      have := abs_lt.1 (hN i j)
      rw [cmp_apply, if_neg (by omega)]; rfl
    exact LinearMap.ext fun x => Prod.ext (funext fun g => this _) (funext fun v => this _)
  · refine Prod.ext (funext fun g => ?_) (funext fun v => ?_) <;> ext i j
    · exact ge (fun q hq => congrArg (·.1 g) (hx q hq)) i j (abs_lt.1 (hN i j)).2
    · exact ge (fun q hq => congrArg (·.2 v) (hx q hq)) i j (abs_lt.1 (hN i j)).2
  · exact tan_lowest Φ S c c₀ m hm hr hn p x hx (fun g => ge fun q hq => congrArg (·.1 g) (h q hq))
      fun v => ge fun q hq => congrArg (·.2 v) (h q hq)

end UpperTheory.V.Ws
end

