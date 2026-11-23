module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimOut
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_lim_hom_out :
    ∀ (G Z ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z], TopFG G → ∀ (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal] (f : ι → G →* Z),
      (∀ i, Continuous (f i)) → (∀ i, K i ≤ (f i).ker) →
      ∃ F : G →* Z, Continuous F ∧ limKer (U : Filter ι) K ≤ F.ker ∧
        (∀ V : OpenNormalSubgroup Z, ∀ᶠ i in (U : Filter ι), ∀ g, (F g)⁻¹ * f i g ∈ V.toSubgroup) ∧
        ((∀ i, Function.Surjective (f i)) → Function.Surjective F) := by
  intro G Z ι _ _ _ _ _ _ _ _ _ _ hG U K _ f hf hK
  obtain ⟨s, hsfin, hsgen⟩ := hG
  obtain ⟨F0, hF0⟩ : ∃ F0 : G → Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F0 g)) := by
    refine ⟨fun g => (U.map (fun i => f i g)).lim, fun g => ?_⟩
    have h := (U.map (fun i => f i g)).le_nhds_lim
    rw [Ultrafilter.coe_map] at h
    exact h
  have hone : F0 1 = 1 :=
    tendsto_nhds_unique (hF0 1) (by simp only [map_one]; exact tendsto_const_nhds)
  have hmul : ∀ a b, F0 (a * b) = F0 a * F0 b := fun a b =>
    tendsto_nhds_unique (hF0 (a * b)) (by simp only [map_mul]; exact (hF0 a).mul (hF0 b))
  obtain ⟨F, hF⟩ : ∃ F : G →* Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F g)) :=
    ⟨{ toFun := F0, map_one' := hone, map_mul' := hmul }, hF0⟩
  have agree : ∀ (V : OpenNormalSubgroup Z) (i j : ι),
      (∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup) → (∀ x ∈ s, (F x)⁻¹ * f j x ∈ V.toSubgroup) →
      ∀ g, (f j g)⁻¹ * f i g ∈ V.toSubgroup := by
    intro V i j hi hj g
    let H : Subgroup G :=
      { carrier := {g | (f j g)⁻¹ * f i g ∈ V.toSubgroup}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul] at *
          have := V.toSubgroup.mul_mem (V.isNormal'.conj_mem _ ha (f j b)⁻¹) hb
          convert this using 1
          group
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq, map_inv] at *
          have := V.isNormal'.conj_mem _ (V.toSubgroup.inv_mem ha) (f j a)
          convert this using 1
          group }
    have hHc : IsClosed (H : Set G) :=
      V.toOpenSubgroup.isClosed.preimage (((hf j).inv).mul (hf i))
    have hsH : Subgroup.closure s ≤ H := by
      rw [Subgroup.closure_le]
      intro x hx
      show (f j x)⁻¹ * f i x ∈ V.toSubgroup
      have := V.toSubgroup.mul_mem (V.toSubgroup.inv_mem (hj x hx)) (hi x hx)
      convert this using 1
      group
    have hg : g ∈ (Subgroup.closure s).topologicalClosure := by
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, hsgen.closure_eq]
      trivial
    exact Subgroup.topologicalClosure_minimal _ hsH hHc hg
  have key : ∀ V : OpenNormalSubgroup Z, ∀ᶠ i in (U : Filter ι), ∀ g, (F g)⁻¹ * f i g ∈ V.toSubgroup := by
    intro V
    have hs : ∀ᶠ i in (U : Filter ι), ∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup := by
      refine (Filter.eventually_all_finite hsfin).2 (fun x _ => ?_)
      have hopen : IsOpen {z : Z | (F x)⁻¹ * z ∈ V.toSubgroup} :=
        V.toOpenSubgroup.isOpen.preimage (continuous_const_mul _)
      exact (hF x).eventually (hopen.mem_nhds (by simp))
    obtain ⟨j, hj⟩ := hs.exists
    filter_upwards [hs] with i hi g
    have hC : IsClosed {z : Z | (f j g)⁻¹ * z ∈ V.toSubgroup} :=
      V.toOpenSubgroup.isClosed.preimage (continuous_const_mul _)
    have h1 : (f j g)⁻¹ * F g ∈ V.toSubgroup :=
      hC.mem_of_tendsto (hF g) (hs.mono fun k hk => agree V k j hk hj g)
    have h2 := agree V i j hi hj g
    have := V.toSubgroup.mul_mem (V.toSubgroup.inv_mem h1) h2
    convert this using 1
    group
  have hFc : Continuous F := by
    apply continuous_of_continuousAt_one F
    rw [ContinuousAt, map_one]
    intro W hW
    obtain ⟨t, htW, hto, h1t⟩ := mem_nhds_iff.1 hW
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hto h1t
    obtain ⟨i, hi⟩ := (key V).exists
    have hmem : {g : G | f i g ∈ V.toSubgroup} ∈ nhds (1 : G) :=
      (V.toOpenSubgroup.isOpen.preimage (hf i)).mem_nhds (by simp)
    refine Filter.mem_map.2 (Filter.mem_of_superset hmem (fun g hg => ?_))
    apply htW
    apply hV
    have := V.toSubgroup.mul_mem hg (V.toSubgroup.inv_mem (hi g))
    change F g ∈ V.toSubgroup
    convert this using 1
    group
  refine ⟨F, hFc, ?_, key, ?_⟩
  · intro g hg
    rw [MonoidHom.mem_ker]
    have hall : ∀ V : OpenNormalSubgroup Z, F g ∈ V.toSubgroup := by
      intro V
      let O : OpenNormalSubgroup G :=
        { toSubgroup := V.toSubgroup.comap F
          isOpen' := V.toOpenSubgroup.isOpen.preimage hFc
          isNormal' := V.isNormal'.comap F }
      rw [mem_limKer] at hg
      obtain ⟨i, hi1, hi2⟩ := ((hg O).and (key V)).exists
      have hle : K i ⊔ (O.toOpenSubgroup : Subgroup G) ≤ V.toSubgroup.comap (f i) := by
        refine sup_le ?_ ?_
        · intro x hx
          have hx' := hK i hx
          rw [MonoidHom.mem_ker] at hx'
          show f i x ∈ V.toSubgroup
          rw [hx']
          exact one_mem _
        · intro x hx
          have hx' : F x ∈ V.toSubgroup := hx
          show f i x ∈ V.toSubgroup
          have := V.toSubgroup.mul_mem hx' (hi2 x)
          convert this using 1
          group
      have hfg : f i g ∈ V.toSubgroup := hle hi1
      have := V.toSubgroup.mul_mem hfg (V.toSubgroup.inv_mem (hi2 g))
      convert this using 1
      group
    by_contra hne
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isOpen_compl_singleton (x := F g)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))
    exact hV (hall V) rfl
  · intro hsurj z
    have hcl : IsClosed (Set.range F) := (isCompact_range hFc).isClosed
    have hz : z ∈ closure (Set.range F) := by
      rw [mem_closure_iff_nhds]
      intro t ht
      have hW : (fun y => z * y) ⁻¹' t ∈ nhds (1 : Z) :=
        (continuous_const_mul z).continuousAt.preimage_mem_nhds (by rwa [mul_one])
      obtain ⟨u, huW, huo, h1u⟩ := mem_nhds_iff.1 hW
      obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one huo h1u
      obtain ⟨i, hi⟩ := (key V).exists
      obtain ⟨g, hg⟩ := hsurj i z
      refine ⟨F g, ?_, g, rfl⟩
      have hv : z⁻¹ * F g ∈ V.toSubgroup := by
        have := V.toSubgroup.inv_mem (hi g)
        rw [hg] at this
        convert this using 1
        group
      have := huW (hV hv)
      simpa using this
    rw [hcl.closure_eq] at hz
    exact hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LocFactor
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

open IsLocalRing in
private theorem complete_of_finite (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [IsLocalRing R'] : IsAdicComplete (maximalIdeal R') R' := by
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R')
        (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P
        (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have h0 : IsAdicComplete (maximalIdeal R) R' := by
    let I := maximalIdeal R
    have hb : Function.Bijective (AdicCompletion.of I R) :=
      AdicCompletion.of_bijective_iff.2 (show IsAdicComplete I R from inferInstance)
    let φ : R ≃ₗ[R] AdicCompletion I R := LinearEquiv.ofBijective (AdicCompletion.of I R) hb
    let e : R' ≃ₗ[R] AdicCompletion I R ⊗[R] R' :=
      (TensorProduct.lid R R').symm.trans (TensorProduct.congr φ (LinearEquiv.refl R R'))
    have h1 : AdicCompletion.of I R 1 = 1 := by
      ext n
      simp
    have hfac : ⇑(AdicCompletion.of I R') =
        ⇑(AdicCompletion.ofTensorProduct I R') ∘ ⇑e := by
      funext x
      have he : e x = (1 : AdicCompletion I R) ⊗ₜ[R] x := by
        simp [e, φ, h1]
      simp [he]
    apply AdicCompletion.of_bijective_iff.1
    rw [hfac]
    exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I R').comp e.bijective
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 h0.toIsPrecomplete)
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }

theorem UpperTheory.V.AlgebraTools.local_factor :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (n : Ideal A) [n.IsMaximal],
      Function.Surjective (algebraMap A (Localization.AtPrime n)) ∧ Module.Finite R (Localization.AtPrime n) ∧
      IsLocalHom (algebraMap R (Localization.AtPrime n)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime n)) (Localization.AtPrime n) ∧
      (Module.Free R A → Module.Free R (Localization.AtPrime n)) ∧
      (∃ e : A, IsIdempotentElem e ∧ (∀ n' : Ideal A, n'.IsMaximal → (e ∉ n' ↔ n' = n)) ∧
        RingHom.ker (algebraMap A (Localization.AtPrime n)) = Ideal.span {1 - e}) ∧
      ∀ (C : Type) [CommRing C] [IsLocalRing C] (f : A →+* C), (IsLocalRing.maximalIdeal C).comap f = n →
        ∃ g : Localization.AtPrime n →+* C, g.comp (algebraMap A _) = f := by
  intro R _ _ _ _ A _ _ _ n hn
  letI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  have hfin : Module.Finite R (Localization.AtPrime n) := GlobalTheory.finite_localization_of_henselian R n
  refine ⟨GlobalTheory.surjective_algebraMap_localization_of_henselian R n, hfin, ⟨fun a ha => ?_⟩,
    complete_of_finite R _, fun hF => ?_, ?_, fun C _ _ f hf => ?_⟩
  · by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal R := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal (Localization.AtPrime n)),
      Ideal.mem_comap] at h1
    exact h1 ha
  · haveI : Module.Flat A (Localization.AtPrime n) := IsLocalization.flat _ n.primeCompl
    haveI : Module.Flat R (Localization.AtPrime n) := Module.Flat.trans R A _
    exact Module.free_of_flat_of_isLocalRing
  · obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian R n
    refine ⟨e, he, H, le_antisymm (fun x hx => ?_) ?_⟩
    · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff n.primeCompl _ x).1 hx
      have heq : e ∉ n := (H n hn).2 rfl
      have hu : IsUnit (e * s + (1 - e)) := by
        by_contra h
        obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits h
        by_cases hen : e ∈ m
        · rw [Submodule.add_mem_iff_right _ (Ideal.mul_mem_right _ _ hen),
            GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he] at hmem
          exact hmem hen
        · rw [Submodule.add_mem_iff_left _
              ((GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he m).2 hen),
            (H m hm).1 hen] at hmem
          exact (hn.isPrime.mem_or_mem hmem).elim heq s.2
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      refine Ideal.mem_span_singleton'.2 ⟨v * x, ?_⟩
      linear_combination x * hv - v * e * hs
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      exact ((IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.map_units _
        (⟨e, (H n hn).2 rfl⟩ : n.primeCompl))).1 (he.map _)).symm
  · have hu : ∀ y : n.primeCompl, IsUnit (f y) := fun y => by
      by_contra h
      have h1 : (y : A) ∈ (IsLocalRing.maximalIdeal C).comap f := h
      rw [hf] at h1
      exact y.2 h1
    exact ⟨IsLocalization.lift hu, IsLocalization.lift_comp hu⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrthonormalLocal
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.sqrt_of_residue {R' : Type} [CommRing R'] [HenselianLocalRing R']
    (h2 : IsUnit (2 : R')) (u : R') (hu : IsUnit u) (hs : IsSquare (residue R' u)) :
    ∃ a : R', a * a = u := by
  obtain ⟨b, hb⟩ := hs
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective b
  have hres : residue R' (a₀ ^ 2 - u) = 0 := by rw [map_sub, map_pow, hb, pow_two, sub_self]
  have ha₀ : IsUnit a₀ := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    intro h0
    have hu0 : residue R' u = 0 := by rw [hb, h0, mul_zero]
    exact (hu.map (residue R')).ne_zero hu0
  have hev : eval a₀ (X ^ 2 - C u) ∈ maximalIdeal R' := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa using hres
  have hd : eval a₀ (derivative (X ^ 2 - C u)) = 2 * a₀ := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X]
    norm_num
  have hdu : IsUnit (eval a₀ (derivative (X ^ 2 - C u))) := by
    rw [hd]
    exact h2.mul ha₀
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C u)
    (monic_X_pow_sub_C u two_ne_zero) a₀ hev hdu
  refine ⟨a, ?_⟩
  have h0 := ha.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at h0
  rw [← pow_two]
  exact sub_eq_zero.mp h0

theorem UpperTheory.V.AlgebraTools.orthonormal_local :
    ∀ {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [HenselianLocalRing R'] (φ : R →+* R') {n : ℕ} (H : Matrix (Fin n) (Fin n) R), IsUnit (2 : R) → Hᵀ = H → IsUnit H.det → (∀ c : Rˣ, IsSquare (residue R' (φ c))) → ∃ P : GL (Fin n) R', (P : Matrix (Fin n) (Fin n) R')ᵀ * H.map φ * P = 1 := by
  intro R R' _ _ _ _ φ n H h2 hT hdet hsq
  obtain ⟨P, c, hP⟩ := UpperTheory.V.AlgebraTools.diag_local H h2 hT hdet
  have h2' : IsUnit (2 : R') := by
    have h := h2.map φ
    rwa [map_ofNat] at h
  have hroot : ∀ i, ∃ a : R', a * a = φ (c i) := fun i =>
    UpperTheory.V.AlgebraTools.sqrt_of_residue h2' _ ((c i).isUnit.map φ) (hsq (c i))
  choose a ha using hroot
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := a i) (by rw [ha i]; exact (c i).isUnit.map φ)
  let D : GL (Fin n) R' :=
    ⟨diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R'), diagonal fun i => a i,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp⟩
  have hmap : ((Matrix.GeneralLinearGroup.map φ P : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      (P : Matrix (Fin n) (Fin n) R).map φ := by
    ext i j
    exact Matrix.GeneralLinearGroup.map_apply φ i j P
  have key : ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
      (P : Matrix (Fin n) (Fin n) R).map φ = diagonal fun i => φ (c i) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hP, diagonal_map (map_zero φ)]
  refine ⟨Matrix.GeneralLinearGroup.map φ P * D, ?_⟩
  rw [Units.val_mul, hmap, Matrix.transpose_mul]
  have hD : ((D : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R') := rfl
  calc ((D : Matrix (Fin n) (Fin n) R'))ᵀ * ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        ((P : Matrix (Fin n) (Fin n) R).map φ * (D : Matrix (Fin n) (Fin n) R'))
      = ((D : Matrix (Fin n) (Fin n) R'))ᵀ * (((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        (P : Matrix (Fin n) (Fin n) R).map φ) * (D : Matrix (Fin n) (Fin n) R') := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [key, hD, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
      convert diagonal_one using 2
      funext i
      rw [← ha i]
      calc ((hau i).unit⁻¹ : R'ˣ).val * (a i * a i) * ((hau i).unit⁻¹ : R'ˣ).val
          = (((hau i).unit⁻¹ : R'ˣ).val * (hau i).unit.val) *
            ((hau i).unit.val * ((hau i).unit⁻¹ : R'ˣ).val) := by
            simp only [IsUnit.unit_spec]; ring
        _ = 1 := by simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProLUnits
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.pow_mem_of_sub_one_mem :
    ∀ (l : ℕ) (E : Type) [Ring E] (J : TwoSidedIdeal E), (l : E) ∈ J → ∀ (j : ℕ) (x : E), x - 1 ∈ J →
      x ^ l ^ j - 1 ∈ (J.asIdeal : Submodule E E) ^ (j + 1) := by
  intro l E _ J hl j x hx
  have key : ∀ y : E, y - 1 ∈ J → ∀ n : ℕ, y ^ n - 1 ∈ J := by
    intro y hy n
    rw [← geom_sum_mul]
    exact J.mul_mem_left _ _ hy
  induction j with
  | zero =>
    rw [pow_zero, pow_one, zero_add, Submodule.pow_one]
    exact TwoSidedIdeal.mem_asIdeal.mpr hx
  | succ j ih =>
    have hy : x ^ l ^ j - 1 ∈ J := key x hx _
    rw [pow_succ, pow_mul, ← mul_geom_sum, Submodule.pow_succ]
    refine Submodule.mul_mem_mul ih ?_
    rw [TwoSidedIdeal.mem_asIdeal]
    have hs : ∑ i ∈ Finset.range l, (x ^ l ^ j) ^ i
        = ∑ i ∈ Finset.range l, ((x ^ l ^ j) ^ i - 1) + (l : E) := by
      simp [Finset.sum_sub_distrib]
    rw [hs]
    exact J.add_mem (sum_mem fun i _ => key _ hy i) hl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.totallyDisconnected_quot :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (K : Subgroup G) [K.Normal], IsClosed (K : Set G) →
      TotallyDisconnectedSpace (G ⧸ K) ∧ (∀ g : G, (∀ O : OpenNormalSubgroup G, g ∈ K ⊔ O.toSubgroup) → g ∈ K) := by
  intro G _ _ _ _ _ N _ hN
  refine ⟨?_, fun x hx => ?_⟩
  · rw [totallyDisconnectedSpace_iff_connectedComponent_one]
    refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    by_contra hx
    have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
    have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
    let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
    have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
    have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
    obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
    exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
  · by_contra hx'
    have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
    have h := hx U
    rw [sup_comm] at h
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp h
    refine hU (U.toSubgroup.inv_mem hy) ?_
    rw [← hyz]
    simpa using hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SubgroupQuot
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.TopFG.subgroup_quot :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G], TopFG G →
      (∀ H : Subgroup G, IsOpen (H : Set G) → TopFG H) ∧
      (∀ (Z : Type) [Group Z] [TopologicalSpace Z] (f : G →* Z), Continuous f → Function.Surjective f → TopFG Z) := by
  intro G _ _ _ _ hG
  obtain ⟨s, hs, hden⟩ := hG
  refine ⟨?_, ?_⟩
  · intro H hH
    haveI : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
    haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    set D := Subgroup.closure s with hD
    haveI : Finite s := hs
    haveI : Group.FG D := inferInstance
    haveI : (H.subgroupOf D).FiniteIndex := inferInstance
    have hfg : Group.FG (H.subgroupOf D) := inferInstance
    obtain ⟨t, ht, htf⟩ := Group.fg_iff.mp hfg
    let φ : H.subgroupOf D →* H :=
      (D.subtype.comp (H.subgroupOf D).subtype).codRestrict H (fun x => x.2)
    refine ⟨φ '' t, htf.image _, ?_⟩
    unfold TopGen
    rw [← MonoidHom.map_closure, ht, ← MonoidHom.range_eq_map]
    rw [dense_iff_inter_open]
    intro U hU hUne
    have hVo : IsOpen ((Subtype.val : H → G) '' U) := hH.isOpenMap_subtype_val U hU
    obtain ⟨x, ⟨y, hyU, rfl⟩, hxD⟩ := hden.inter_open_nonempty _ hVo (hUne.image _)
    refine ⟨y, hyU, ⟨⟨y.1, hxD⟩, y.2⟩, ?_⟩
    rfl
  · intro Z _ _ f hf hsurj
    refine ⟨f '' s, hs.image _, ?_⟩
    unfold TopGen at hden ⊢
    rw [← MonoidHom.map_closure, Subgroup.coe_map]
    exact hsurj.denseRange.dense_image hf hden
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraFin
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ultra_fin :
    ∀ (ι Z : Type) (U : Ultrafilter ι) (a : ι → Z) (s : Set Z), s.Finite → (∀ᶠ i in (U : Filter ι), a i ∈ s) →
      ∃! z, z ∈ s ∧ ∀ᶠ i in (U : Filter ι), a i = z := by
  intro ι Z U a s hs h
  have hsub : {i | a i ∈ s} ⊆ ⋃ z ∈ s, {i | a i = z} := by
    intro i hi
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨a i, hi, rfl⟩
  have hmem : (⋃ z ∈ s, {i | a i = z}) ∈ U := U.1.sets_of_superset h hsub
  obtain ⟨z, hz, hzU⟩ := (Ultrafilter.finite_biUnion_mem_iff hs).1 hmem
  refine ⟨z, ⟨hz, hzU⟩, ?_⟩
  rintro w ⟨-, hw⟩
  obtain ⟨i, hi1, hi2⟩ := (hw.and hzU).exists
  exact hi1.symm.trans hi2
end

