module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Ideal.GoingDown

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CoCoprod
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem co_coprod_pres (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] :
    ∃ W : WPres O Unit R, ∀ s, W.z s ∈ maximalIdeal R := by
  obtain ⟨n, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (maximalIdeal R))
  have hm : ∀ s, z s ∈ maximalIdeal R := fun s => hz ▸ Submodule.subset_span ⟨s, rfl⟩
  haveI : IsCO O (MvPowerSeries (Fin n) O) := co_mvps O O (Fin n)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O R (Fin n) (Algebra.ofId _ _) z hm
  refine ⟨⟨Fin n, fun _ => (), F, ?_, ?_⟩, fun s => ?_⟩
  · refine co_surj O _ R _ (le_trans ?_ le_sup_left)
    rw [← hz, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [← hF s]
    refine Ideal.mem_map_of_mem _ fun hu => ?_
    simpa using MvPowerSeries.isUnit_constantCoeff _ hu
  · intro g hg j
    have : wcomp O (fun _ : Fin n => ()) j g = g := by
      ext a
      rw [coeff_wcomp, if_pos (Subsingleton.elim _ _)]
    rwa [this]
  · show F (MvPowerSeries.X s) ∈ _
    rw [hF]
    exact hm s

theorem UpperTheory.V.CA.co_coprod :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (T : Type) [Finite T] (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra O (B t)] [∀ t, IsCO O (B t)], ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (j : ∀ t, B t →ₐ[O] R), ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : ∀ t, B t →ₐ[O] R'), ∃! g : R →ₐ[O] R', ∀ t, g.comp (j t) = f t := by
  intro O _ _ _ _ T _ B _ _ _
  haveI := Fintype.ofFinite T
  choose WB hWB using fun t => co_coprod_pres O (B t)
  obtain ⟨R, i1, i2, i3, i, _, _, h, -⟩ := UpperTheory.V.Alg.coprod O Unit T B WB hWB
  exact ⟨R, i1, i2, i3, i, h⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplQuot
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem precomplete_quot {R : Type} [CommRing R] (I K : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I (R ⧸ K) := by
  have hmap : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R).map K.mkQ = (I ^ n • ⊤ : Submodule R (R ⧸ K)) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  refine ⟨fun f hf => ?_⟩
  have hd : ∀ n, ∃ d ∈ (I ^ n • ⊤ : Submodule R R), K.mkQ d = f (n + 1) - f n := by
    intro n
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, ← hmap] at h
    exact h
  choose d hd hd' using hd
  obtain ⟨a, ha⟩ := K.mkQ_surjective (f 0)
  let g : ℕ → R := fun n => a + ∑ i ∈ Finset.range n, d i
  have hg : ∀ n, K.mkQ (g n) = f n := by
    intro n
    induction n with
    | zero => simpa [g] using ha
    | succ n ih =>
      have : g (n + 1) = g n + d n := by simp only [g, Finset.sum_range_succ, add_assoc]
      rw [this, map_add (f := _), ih, hd']; abel
  have hc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro m n h
    induction h with
    | refl => rfl
    | @step n h ih =>
      have : g (n + 1) = g n + d n := by simp only [g, Finset.sum_range_succ, add_assoc]
      refine ih.trans ?_
      rw [SModEq.sub_mem, this, sub_add_cancel_left]
      exact neg_mem (Submodule.smul_mono_left (Ideal.pow_le_pow_right h) (hd n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hc
  refine ⟨K.mkQ L, fun n => ?_⟩
  rw [SModEq.sub_mem, ← hg, ← map_sub, ← hmap]
  exact Submodule.mem_map_of_mem (SModEq.sub_mem.1 (hL n))

theorem UpperTheory.V.CA.cpl_quot :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → ∀ (C' R' : Type) [CommRing C'] [CommRing R'] [Algebra C' R'] [IsLocalRing R'] (π : C →+* C') (x' : Ideal C'), Function.Surjective π → x'.comap π = x → IsCplAt x' R' → ∃ F : R →+* R', Function.Surjective F ∧ F.comp (algebraMap C R) = (algebraMap C' R').comp π ∧ RingHom.ker F = (RingHom.ker π).map (algebraMap C R) := by
  intro C R _ _ _ _ _ x hx hR C' R' _ _ _ _ π x' hπ hx' hR'
  haveI : IsNoetherianRing C' := isNoetherianRing_of_surjective C C' π hπ
  have hxm : x.map π = x' := by rw [← hx', Ideal.map_comap_of_surjective π hπ]
  haveI hx'm : x'.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective π hπ hx with h | h
    · rw [hxm] at h
      exact absurd (by rw [← hx', h, Ideal.comap_top]) hx.ne_top
    · rwa [hxm] at h
  haveI := hR.noeth
  haveI := hR.complete
  haveI := hR'.complete
  obtain ⟨hU, -, hm⟩ := cpl_uniq x hR
  obtain ⟨hU', -, hm'⟩ := cpl_uniq x' hR'
  have hx1 : x' ≤ (maximalIdeal R').comap (algebraMap C' R') := by
    rw [← Ideal.map_le_iff_le_comap, hm']
  obtain ⟨F, ⟨hF, hFm⟩, -⟩ := hU R' (maximalIdeal R') ((algebraMap C' R').comp π) (by
    rw [← Ideal.comap_comap, ← hx']; exact Ideal.comap_mono hx1)
  set K := (RingHom.ker π).map (algebraMap C R) with hK
  have hKF : K ≤ RingHom.ker F := by
    rw [hK, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [RingHom.mem_ker] at hc
    have := RingHom.congr_fun hF c
    simp only [RingHom.comp_apply, hc, map_zero] at this
    exact this
  set J := (maximalIdeal R).map (Ideal.Quotient.mk K) with hJ
  haveI : IsAdicComplete J (R ⧸ K) := by
    haveI := precomplete_quot (maximalIdeal R) K
    haveI : IsHausdorff (maximalIdeal R) (R ⧸ K) :=
      IsHausdorff.of_le_jacobson _ _ (ringJacobson_eq_maximalIdeal R).ge
    exact (IsAdicComplete.map_algebraMap_iff (S := R ⧸ K) (maximalIdeal R) (R ⧸ K)).2 ⟨⟩
  let g : C' →+* R ⧸ K := π.liftOfSurjective hπ ⟨(Ideal.Quotient.mk K).comp (algebraMap C R), fun c hc => by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hc⟩
  have hg : g.comp π = (Ideal.Quotient.mk K).comp (algebraMap C R) := RingHom.liftOfSurjective_comp _ _ _
  have hxJ : x ≤ J.comap ((Ideal.Quotient.mk K).comp (algebraMap C R)) := by
    rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_map, hm]
  obtain ⟨G, ⟨hG, hGm⟩, -⟩ := hU' (R ⧸ K) J g (by
    rw [← hxm, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hg]; exact hxJ)
  have h1 : G.comp F = Ideal.Quotient.mk K := by
    refine (hU (R ⧸ K) J _ hxJ).unique ⟨?_, ?_⟩ ⟨rfl, Ideal.le_comap_map⟩
    · rw [RingHom.comp_assoc, hF, ← RingHom.comp_assoc, hG, hg]
    · rw [← Ideal.comap_comap]; exact hFm.trans (Ideal.comap_mono hGm)
  let Fb : R ⧸ K →+* R' := Ideal.Quotient.lift K F hKF
  have hFb : Fb.comp (Ideal.Quotient.mk K) = F := RingHom.ext fun _ => rfl
  have h2 : Fb.comp G = RingHom.id R' := by
    refine (hU' R' (maximalIdeal R') _ hx1).unique ⟨?_, ?_⟩ ⟨rfl, le_rfl⟩
    · rw [RingHom.comp_assoc, hG, ← RingHom.cancel_right hπ, RingHom.comp_assoc, hg, ← RingHom.comp_assoc, hFb, hF]
    · rw [← Ideal.comap_comap]
      refine hGm.trans (Ideal.comap_mono ?_)
      rw [hJ, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hFb]
      exact hFm
  refine ⟨F, fun y => ?_, hF, le_antisymm (fun r hr => ?_) hKF⟩
  · obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (G y)
    refine ⟨r, ?_⟩
    have := RingHom.congr_fun h2 y
    rw [RingHom.comp_apply, ← hr] at this
    exact this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← h1, RingHom.comp_apply, (RingHom.mem_ker).1 hr, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem UpperTheory.V.CA.d_tr_coeff {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (x : E) (i : ℕ) (hi : i ≤ n) : (D.D A[X] (1 + X ⊗ₜ x)).coeff i = D.lam i x := by
  rw [(d_chi D x).2.2.1, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff, hi]

private theorem UpperTheory.V.CA.d_tr_dual {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (hn : 1 ≤ n) (x : E) :
    D.D (DualNumber A) (1 + DualNumber.eps ⊗ₜ x) = 1 + D.tr x • DualNumber.eps := by
  have h := D.nat A[X] (DualNumber A) (aeval DualNumber.eps) (1 + X ⊗ₜ x)
  rw [map_add (f := _), map_one, Algebra.TensorProduct.map_tmul, aeval_X, AlgHom.id_apply] at h
  rw [h, (d_chi D x).2.2.1]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', (d_chi D x).1]
  have h2 : ∀ k : ℕ, (DualNumber.eps : DualNumber A) ^ (k + 1 + 1) = 0 := fun k => by
    rw [pow_succ, pow_succ, mul_assoc, DualNumber.eps_mul_eps, mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, aeval_X, aeval_C, h2, mul_zero, Finset.sum_const_zero]
  simp [Det.tr, Algebra.smul_def, add_comm]

theorem UpperTheory.V.CA.d_tr :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), (1 ≤ n → ∃ t : E →ₗ[A] A, ∀ x, t x = D.tr x) ∧ (∀ i x y, D.lam i (x * y) = D.lam i (y * x)) ∧ (1 ≤ n → D.tr 1 = n) := by
  intro n A E _ _ _ D
  refine ⟨fun hn => ⟨⟨⟨D.tr, fun x y => ?_⟩, fun a x => ?_⟩, fun _ => rfl⟩, fun i x y => ?_, fun hn => ?_⟩
  · have h : (1 + DualNumber.eps ⊗ₜ (x + y) : DualNumber A ⊗[A] E) =
        (1 + DualNumber.eps ⊗ₜ x) * (1 + DualNumber.eps ⊗ₜ y) := by
      rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, DualNumber.eps_mul_eps, zero_tmul,
        tmul_add]
      simp only [one_mul, mul_one, add_zero]
      abel
    have h2 := congrArg (D.D (DualNumber A)) h
    rw [map_mul, d_tr_dual D hn, d_tr_dual D hn, d_tr_dual D hn] at h2
    have h3 := congrArg TrivSqZeroExt.snd h2
    simpa [add_comm] using h3
  · simpa [Det.tr] using (d_chi D x).2.2.2.2.2.2 a 1 hn
  · have h : ∀ j ≤ n, D.lam j (x * y) = D.lam j (y * x) := fun j hj => by
      have := d_comm D A[X] (X ⊗ₜ x) (1 ⊗ₜ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
      rw [← d_tr_coeff D _ j hj, ← d_tr_coeff D _ j hj, this]
    have h2 : D.chi (x * y) = D.chi (y * x) := by
      rw [(d_chi D (x * y)).2.1, (d_chi D (y * x)).2.1]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
    rw [Det.lam, Det.lam, h2]
  · rw [Det.tr, ← d_tr_coeff D 1 1 hn]
    have h : (1 + X ⊗ₜ 1 : A[X] ⊗[A] E) = (1 + X : A[X]) • 1 := by
      rw [Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one, add_tmul]
    simp only [h, D.homog, map_one, mul_one, coeff_one_add_X_pow, Nat.choose_one_right]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DUnit
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_unit :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), D.IsCH → (∀ x, IsUnit x ↔ IsUnit (D.val x)) ∧ Algebra.IsIntegral A E := by
  intro n A E _ _ _ D hD
  have h0 : ∀ x : E, Polynomial.aeval x (D.chi x) = 0 := ((d_chS D A).2.2 hD).2
  refine ⟨fun x => ⟨fun h => h.map D.val, fun h => ?_⟩, ⟨fun x => ?_⟩⟩
  · have h1 : D.lam n x = D.val x := (d_chi D x).2.2.2.1
    rw [← h1, Det.lam, Nat.sub_self] at h
    have hc : IsUnit ((D.chi x).coeff 0) := isUnit_of_mul_isUnit_right h
    have h2 := h0 x
    rw [← Polynomial.X_mul_divX_add (D.chi x), map_add (f := _), map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C] at h2
    have h3 : IsUnit (x * Polynomial.aeval x (D.chi x).divX) := by
      rw [eq_neg_of_add_eq_zero_left h2]
      exact (hc.map (algebraMap A E)).neg
    have h4 : Commute x (Polynomial.aeval x (D.chi x).divX) := by
      have := (Commute.all (X : A[X]) (D.chi x).divX).map (Polynomial.aeval x)
      rwa [Polynomial.aeval_X] at this
    exact (h4.isUnit_mul_iff.1 h3).1
  · exact ⟨D.chi x, (d_chi D x).2.2.2.2.1, h0 x⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

private theorem dker_poly_eq (S : Type) [CommRing S] [Algebra A S] (p q : S[X] ⊗[A] E)
    (H : ∀ (T : Type) [CommRing T] [Algebra A T] (f : S[X] →ₐ[A] T), IsNilpotent (f X) →
      D.D T (Algebra.TensorProduct.map f (AlgHom.id A E) p) =
        D.D T (Algebra.TensorProduct.map f (AlgHom.id A E) q)) :
    D.D S[X] p = D.D S[X] q := by
  ext k
  have h := H _ (Ideal.Quotient.mkₐ A (Ideal.span {(X : S[X]) ^ (k + 1)})) ⟨k + 1, by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩
  rw [D.nat, D.nat] at h
  have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  have h3 := X_pow_dvd_iff.1 h2 k (Nat.lt_succ_self k)
  rwa [coeff_sub, sub_eq_zero] at h3

private theorem dker_unit (T : Type) [CommRing T] [Algebra A T] (t : T) (ht : IsNilpotent t) (w : T ⊗[A] E) :
    IsUnit (1 + (t ⊗ₜ[A] (1 : E)) * w) := by
  apply IsNilpotent.isUnit_one_add
  obtain ⟨k, hk⟩ := ht
  have : (t ⊗ₜ[A] (1 : E)) * w = t • w := by rw [Algebra.smul_def]; rfl
  exact ⟨k, by rw [this, _root_.smul_pow, hk, zero_smul]⟩

private theorem dker_cancel (S : Type) [CommRing S] [Algebra A S] (w : S ⊗[A] E) :
    Det.cancel A E S S[X] (1 + X ⊗ₜ w) = 1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) w := by
  rw [map_add (f := _), map_one]
  congr 1

private theorem dker_top (S : Type) [CommRing S] [Algebra A S] (w : S ⊗[A] E) :
    (D.D S[X] (1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) w)).coeff n = D.D S w := by
  obtain ⟨h1, h2, -⟩ := d_bc D S
  obtain ⟨-, -, h3, h4, -⟩ := d_chi (D.baseChange S) w
  rw [← dker_cancel, ← h1, h3, ← h2, ← h4, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  simp

private theorem dker_of_kills {x : E} (hx : D.Kills x) : x ∈ D.ker := by
  rw [Det.mem_ker]
  intro S _ _ y u v
  rw [← dker_top, ← dker_top D S y]
  apply congrArg (fun p : S[X] => p.coeff n)
  apply dker_poly_eq
  intro T _ _ f hf
  simp only [map_add (f := _), map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) y) = y'
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) u) = u'
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) v) = v'
  obtain ⟨c, hc⟩ := dker_unit T (f X) hf y'
  have e : 1 + (f X ⊗ₜ[A] (1 : E)) * (y' + u' * (1 ⊗ₜ x) * v') =
      (c : T ⊗[A] E) * (1 + ((↑c⁻¹ : T ⊗[A] E) * (f X ⊗ₜ[A] (1 : E)) * u' * (1 ⊗ₜ x)) * v') := by
    rw [mul_add, mul_add, ← add_assoc, ← hc]
    simp only [← mul_assoc, Units.mul_inv, one_mul, mul_one]
  rw [e, map_mul, d_comm, ← mul_assoc, hx, mul_one, hc]

private theorem dker_kills_of {x : E}
    (hx : ∀ (S : Type) [CommRing S] [Algebra A S] (s : S) (y : S ⊗[A] E), D.D S (y + s ⊗ₜ x) = D.D S y) :
    D.Kills x := by
  intro S _ _ h
  have key : D.D S[X] (1 + (1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) * (1 ⊗ₜ x)) =
      D.D S[X] 1 := by
    apply dker_poly_eq
    intro T _ _ f hf
    simp only [map_add (f := _), map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) = h'
    obtain ⟨c, hc⟩ := dker_unit T (f X) hf h'
    have e : 1 + (c : T ⊗[A] E) * (1 ⊗ₜ x) = (c : T ⊗[A] E) * ((↑c⁻¹ : T ⊗[A] E) + 1 ⊗ₜ x) := by
      rw [mul_add, Units.mul_inv]
    rw [← hc, e, map_mul, hx, ← map_mul, Units.mul_inv, map_one]
  let ev : S[X] →ₐ[A] S := (Polynomial.aeval (R := S) (1 : S)).restrictScalars A
  have hev : Algebra.TensorProduct.map ev (AlgHom.id A E)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) = h := by
    clear key
    induction h with
    | tmul b z => simp [ev]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hX : ev X = 1 := by simp [ev]
  have k2 := congrArg ev key
  rw [← D.nat, map_one, map_one] at k2
  simp only [map_add (f := _), map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hev, hX] at k2
  rw [← Algebra.TensorProduct.one_def, one_mul, add_mul, one_mul, add_comm (_ ⊗ₜ x), ← add_assoc, hx] at k2
  exact k2

end

theorem UpperTheory.V.CA.d_ker :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), (x ∈ D.ker ↔ D.Kills x) ∧ (x ∈ D.ker ↔ ∀ (S : Type) [CommRing S] [Algebra A S] (s : S) (y : S ⊗[A] E), D.D S (y + s ⊗ₜ x) = D.D S y) ∧ (x ∈ D.ker → ∀ h i, 1 ≤ i → i ≤ n → D.lam i (h * x) = 0) := by
  intro n A E _ _ _ D x
  refine ⟨⟨fun hx S _ _ h => ?_, dker_of_kills D⟩,
    ⟨fun hx S _ _ s y => ?_, fun hx => dker_of_kills D (dker_kills_of D hx)⟩, fun hx h i h1 hi => ?_⟩
  · simpa using D.mem_ker.1 hx S 1 h 1
  · simpa using D.mem_ker.1 hx S y (s ⊗ₜ 1) 1
  · obtain ⟨-, -, h3, -⟩ := d_chi D (h * x)
    have h4 : D.D A[X] (1 + X ⊗ₜ (h * x)) = 1 := by
      simpa using D.mem_ker.1 hx A[X] 1 (X ⊗ₜ h) 1
    have h5 := congrArg (fun p => p.coeff i) (h3.symm.trans h4)
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_one] at h5
    simpa [Nat.lt_succ_of_le hi, show i ≠ 0 by omega] using h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GChmap
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem mem_iff {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] [Algebra A B] (D : GDet n A G)
    (x : MonoidAlgebra B G) :
    x ∈ TwoSidedIdeal.span (D.map (algebraMap A B)).CH ↔ toT A G B x ∈
      Submodule.span B ((fun z : MonoidAlgebra A G => (1 : B) ⊗ₜ[A] z) ''
        (TwoSidedIdeal.span D.CH : Set (MonoidAlgebra A G))) := by
  rw [← d_toDet_CH, ← d_toDet_CH, d_toDet_map, ← SetLike.mem_coe (p := Submodule.span B _),
    ← (d_chS D.toDet B).2.1, SetLike.mem_coe]
  obtain ⟨-, -, h1, h2⟩ := d_pull (D.toDet.baseChange B) (toT A G B)
  refine ⟨h1 x, fun h => ?_⟩
  obtain ⟨y, hy, e⟩ := (h2 fun z => ⟨_, toT_ofT z⟩).2 _ h
  have : y = x := by rw [← ofT_toT (A := A) y, e, ofT_toT]
  exact this ▸ hy

private theorem map_mem {A B : Type} [Ring A] [Ring B] (f : A →+* B) (S : Set A) (z : A)
    (hz : z ∈ TwoSidedIdeal.span S) : f z ∈ TwoSidedIdeal.span (f '' S) := by
  induction hz using TwoSidedIdeal.span_induction with
  | mem x hx => exact TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | left_absorb a x _ hx => rw [map_mul]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  | right_absorb b x _ hx => rw [map_mul]; exact TwoSidedIdeal.mul_mem_right _ _ _ hx

theorem UpperTheory.V.CA.g_chmap :
    ∀ {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B), TwoSidedIdeal.span (D.map f).CH = TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G f '' D.CH) := by
  intro n A B G _ _ _ D f
  letI : Algebra A B := f.toAlgebra
  change TwoSidedIdeal.span (D.map (algebraMap A B)).CH =
    TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap A B) '' D.CH)
  have e : ∀ z : MonoidAlgebra A G, ofT A G B (1 ⊗ₜ z) = MonoidAlgebra.mapRingHom G (algebraMap A B) z :=
    fun z => by rw [ofT_tmul, one_smul]
  apply le_antisymm
  · intro x hx
    rw [mem_iff] at hx
    rw [← ofT_toT (A := A) x]
    generalize toT A G B x = w at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      rw [e]
      exact map_mem _ _ z hz
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  · rw [TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_iff, ← e, toT_ofT]
    exact Submodule.subset_span ⟨z, TwoSidedIdeal.subset_span hz, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightSpaceFinite
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

theorem UpperTheory.V.CA.c3a :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → Module.Flat C R ∧ (∀ p : Ideal C, p.IsPrime → p ≤ x → ∃ q : Ideal R, q.IsPrime ∧ q.comap (algebraMap C R) = p) ∧ (∀ q : Ideal R, q.IsPrime → q.comap (algebraMap C R) ≤ x) ∧ (∀ q ∈ minimalPrimes R, q.comap (algebraMap C R) ∈ minimalPrimes C) ∧ ∀ (I : Ideal C), ∀ q ∈ (I.map (algebraMap C R)).minimalPrimes, q.comap (algebraMap C R) ∈ I.minimalPrimes := by
  intro C R _ _ _ _ _ x _ h
  obtain ⟨-, ⟨e⟩, -⟩ := UpperTheory.V.CA.cpl_uniq x h
  have hflat : Module.Flat C R := by
    have h1 : Module.Flat (Localization.AtPrime x) (Cpl x) := inferInstance
    have h2 : Module.Flat C (Localization.AtPrime x) := IsLocalization.flat _ x.primeCompl
    have h3 : Module.Flat C (Cpl x) := Module.Flat.trans C (Localization.AtPrime x) (Cpl x)
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  have hx : (maximalIdeal R).comap (algebraMap C R) = x := by simpa using h.comap_pow 1
  have gd : ∀ (p : Ideal C) (q : Ideal R), p.IsPrime → q.IsPrime → p ≤ q.comap (algebraMap C R) →
      ∃ Q : Ideal R, Q ≤ q ∧ Q.IsPrime ∧ Q.comap (algebraMap C R) = p := by
    intro p q hp hq hle
    haveI : q.LiesOver (q.comap (algebraMap C R)) := ⟨rfl⟩
    obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le q hle
    exact ⟨Q, hQ, hQp, hQo.over.symm⟩
  have hmin : ∀ (I : Ideal C), ∀ q ∈ (I.map (algebraMap C R)).minimalPrimes,
      q.comap (algebraMap C R) ∈ I.minimalPrimes := by
    intro I q hq
    haveI : q.IsPrime := hq.1.1
    refine ⟨⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.1 hq.1.2⟩, ?_⟩
    rintro p ⟨hp, hIp⟩ hle
    obtain ⟨Q, hQ, hQp, hQo⟩ := gd p q hp this hle
    have : q ≤ Q := hq.2 ⟨hQp, Ideal.map_le_iff_le_comap.2 (hQo ▸ hIp)⟩ hQ
    rw [← hQo]
    exact Ideal.comap_mono this
  refine ⟨hflat, ?_, ?_, ?_, hmin⟩
  · intro p hp hle
    obtain ⟨Q, -, hQp, hQo⟩ := gd p (maximalIdeal R) hp inferInstance (hx.symm ▸ hle)
    exact ⟨Q, hQp, hQo⟩
  · intro q hq
    rw [← hx]
    exact Ideal.comap_mono (le_maximalIdeal hq.ne_top)
  · intro q hq
    apply hmin ⊥ q
    rw [Ideal.map_bot]
    exact hq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KMem
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.k_mem :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), Polynomial.aeval x (D.chi x) ∈ D.CH := by
  intro n A E _ _ _ D x
  have key : ∀ w ∈ Submodule.span A ((fun z : E => (1 : A) ⊗ₜ[A] z) '' (D.CH : Set E)),
      Algebra.TensorProduct.lid A E w ∈ D.CH := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a y _ hy => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hy
  have h1 := (d_chS D A).1 (1 ⊗ₜ x)
  have h2 : D.chiS A (1 ⊗ₜ x) = D.chi x := by simp [Det.chiS, Det.chi]
  rw [h2] at h1
  have h3 := key _ h1
  rw [← Polynomial.aeval_algHom_apply] at h3
  simpa using h3
end

