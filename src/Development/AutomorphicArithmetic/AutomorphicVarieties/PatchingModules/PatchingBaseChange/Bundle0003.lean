module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SsDescend
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem eq_bot_of_forall_isNilpotent_of_isSemisimple {R : Type*} [Ring R] [IsSemisimpleRing R] (L : Submodule R R)
    (h : ∀ z ∈ L, IsNilpotent z) : L = ⊥ := by
  obtain ⟨C, hC⟩ := exists_isCompl L
  have h1 : (1 : R) ∈ L ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have key : ∀ l ∈ L, l * f = 0 := by
    intro l hl
    have hl1 : l * e ∈ L := L.smul_mem l he
    have hl2 : l * f ∈ C := C.smul_mem l hf
    have hsub : l * f = l - l * e := by
      rw [eq_sub_iff_add_eq, add_comm, ← mul_add, hef, mul_one]
    have hL : l * f ∈ L := by rw [hsub]; exact L.sub_mem hl hl1
    exact (Submodule.disjoint_def.mp hC.disjoint) _ hL hl2
  have hee : IsIdempotentElem e := by
    show e * e = e
    calc e * e = e * (e + f) := by rw [mul_add, key e he, add_zero]
      _ = e := by rw [hef, mul_one]
  have he0 : e = 0 := hee.eq_zero_of_isNilpotent (h e he)
  rw [eq_bot_iff]
  intro l hl
  have hl' : l = l * e + l * f := by rw [← mul_add, hef, mul_one]
  rw [Submodule.mem_bot, hl', key l hl, he0, mul_zero, add_zero]

theorem UpperTheory.V.Pa.BC.ss_descend :
    ∀ (κ κ' E : Type) [Field κ] [Field κ'] [Algebra κ κ'] [Ring E] [Algebra κ E] [Module.Finite κ E], IsSemisimpleRing (κ' ⊗[κ] E) → IsSemisimpleRing E := by
  intro κ κ' E _ _ _ _ _ _ hT
  haveI : IsArtinianRing E := IsArtinianRing.of_finite κ E
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := E)
  set J := Ring.jacobson E with hJ
  let S : ℕ → Submodule κ (κ' ⊗[κ] E) := fun k =>
    Submodule.span κ {z | ∃ c : κ', ∃ a ∈ J ^ k, z = c ⊗ₜ[κ] a}
  have hgen : ∀ k (c : κ') (a : E), a ∈ J ^ k → c ⊗ₜ[κ] a ∈ S k :=
    fun k c a ha => Submodule.subset_span ⟨c, a, ha, rfl⟩
  have hmul : ∀ a (z w : κ' ⊗[κ] E), z ∈ S a → w ∈ S 1 → z * w ∈ S (a + 1) := by
    intro a z w hz hw
    induction hz using Submodule.span_induction with
    | mem z hz =>
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨c, u, hu, rfl⟩ := hz
        obtain ⟨c', v, hv, rfl⟩ := hw
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        refine hgen _ _ _ ?_
        rw [Submodule.pow_succ]
        rw [Submodule.pow_one] at hv
        exact Ideal.mul_mem_mul hu hv
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add w₁ w₂ _ _ h₁ h₂ => rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
      | smul r w _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ r h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
    | smul r z _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r h
  have hbot : S n = ⊥ := by
    rw [eq_bot_iff, Submodule.span_le]
    rintro z ⟨c, a, ha, rfl⟩
    rw [hn, Ideal.zero_eq_bot, Submodule.mem_bot] at ha
    show _ ∈ (⊥ : Submodule κ (κ' ⊗[κ] E))
    rw [Submodule.mem_bot, ha, TensorProduct.tmul_zero]
  have h1 : ∀ t : κ' ⊗[κ] E, t * ((1 : κ') ⊗ₜ[κ] x) ∈ S 1 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | tmul c a =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      refine hgen 1 c _ ?_
      rw [Submodule.pow_one]
      exact J.mul_mem_left a hx
    | add t₁ t₂ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  have hpow : ∀ z ∈ S 1, ∀ k, z ^ k ∈ S k := by
    intro z hz k
    induction k with
    | zero =>
      rw [pow_zero, Algebra.TensorProduct.one_def]
      exact hgen 0 1 1 (Submodule.one_le.mp fun _ h => h)
    | succ k ih => rw [pow_succ]; exact hmul k _ _ ih hz
  have hL : Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x} = ⊥ := by
    apply eq_bot_of_forall_isNilpotent_of_isSemisimple
    intro z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨n, ?_⟩
    have hz' := hpow _ (h1 t) n
    rw [hbot, Submodule.mem_bot] at hz'
    rw [smul_eq_mul]
    exact hz'
  have hy : (1 : κ') ⊗ₜ[κ] x = 0 := by
    have hm : (1 : κ') ⊗ₜ[κ] x ∈ Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x} :=
      Submodule.mem_span_singleton_self _
    rw [hL, Submodule.mem_bot] at hm
    exact hm
  apply Algebra.TensorProduct.includeRight_injective (R := κ) (A := κ') (B := E)
    (algebraMap κ κ').injective
  rw [Algebra.TensorProduct.includeRight_apply, map_zero, hy]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.StarMap
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.star_map :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing O'] [Algebra ℤ_[l] O'] (R R' : Type) [CommRing R] [Algebra O R] [CommRing R'] [Algebra O' R'] (g : R →+* R'), (∀ a : ℤ_[l], g (algebraMap O R (algebraMap ℤ_[l] O a)) = algebraMap O' R' (algebraMap ℤ_[l] O' a)) → (pushCh g (F.eps O R) = F.eps O' R') ∧ (∀ n y, MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n y) = F.star O' R' n (MonoidAlgebra.mapRingHom F.G₀ g y)) ∧ ∀ (n : ℕ) (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ) (γ : Fin n → F.Gv v), MonoidAlgebra.mapRingHom F.G₀ g (F.oEl v ψ γ) = F.oEl v (fun i => pushCh g (ψ i)) γ := by
  intro l _ F O O' _ _ _ _ R R' _ _ _ _ g hg
  have h1 : pushCh g (F.eps O R) = F.eps O' R' := by
    ext x
    simp [GFrame.eps, pushCh, hg]
  have hs : ∀ (S : Type) [CommRing S] [Algebra O S] (n : ℕ) (h : F.G₀) (r : S), F.star O S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ n h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hs' : ∀ (S : Type) [CommRing S] [Algebra O' S] (n : ℕ) (h : F.G₀) (r : S), F.star O' S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O' S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ n h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hadd : ∀ (n : ℕ) (a b : MonoidAlgebra R F.G₀), F.star O R n (a + b) = F.star O R n a + F.star O R n b := by
    intro n a b
    simp [GFrame.star]
  have hadd' : ∀ (n : ℕ) (a b : MonoidAlgebra R' F.G₀), F.star O' R' n (a + b) = F.star O' R' n a + F.star O' R' n b := by
    intro n a b
    simp [GFrame.star]
  have hz : ∀ (n : ℕ), F.star O R n 0 = 0 := by
    intro n
    simp [GFrame.star]
  have hz' : ∀ (n : ℕ), F.star O' R' n 0 = 0 := by
    intro n
    simp [GFrame.star]
  have he : ∀ (h : F.G₀) (k : ℤ), g ((F.eps O R h ^ k : Rˣ) : R) = ((F.eps O' R' h ^ k : R'ˣ) : R') := by
    intro h k
    rw [← h1, pushCh, MonoidHom.comp_apply, ← map_zpow (Units.map (g : R →* R'))]
    rfl
  refine ⟨h1, ?_, ?_⟩
  · intro n y
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [hz, map_zero, hz']
    | add a b ha hb => rw [hadd, map_add (f := _), ha, hb, map_add (f := _), hadd']
    | single h r =>
      rw [hs, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, hs', map_mul, he]
  · intro n v ψ γ
    simp only [GFrame.oEl, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp [Function.comp_def, map_sub, MonoidAlgebra.mapRingHom_single, pushCh]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilCo
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_co :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsCO O R], ∃ _ : IsCO O' (Til O O' R), IsLocalHom (Til.ι O O' R) ∧ Til.s O O' R ∈ maximalIdeal (Til O O' R) := by
  intro O O' _ _ _ _ _ _ _ R _ _ _
  haveI hT := UpperTheory.V.CA.cl_bc O O' R
  let f : R →+* O' ⊗[O] R := (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom
  have hint : f.IsIntegral := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact f.isIntegralElem_zero
    | tmul o r =>
      have ho : IsIntegral O ((Algebra.TensorProduct.includeLeft : O' →ₐ[O] O' ⊗[O] R) o) :=
        (Algebra.IsIntegral.isIntegral (R := O) o).map _
      rw [Algebra.TensorProduct.includeLeft_apply] at ho
      obtain ⟨p, hp, hpe⟩ := ho
      have h1 : f.IsIntegralElem (o ⊗ₜ[O] (1 : R)) := by
        refine ⟨p.map (algebraMap O R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hc : f.comp (algebraMap O R) = algebraMap O (O' ⊗[O] R) :=
          (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).comp_algebraMap
        rw [hc]
        exact hpe
      have he : o ⊗ₜ[O] r = (o ⊗ₜ[O] (1 : R)) * f r := by
        show _ = _ * ((1 : O') ⊗ₜ[O] r)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [he]
      exact RingHom.IsIntegralElem.mul f h1 f.isIntegralElem_map
    | add x y hx hy => exact RingHom.IsIntegralElem.add f hx hy
  have hloc : IsLocalHom f := by
    refine ((IsLocalRing.local_hom_tfae f).out 1 5).mpr ?_
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hint (maximalIdeal (O' ⊗[O] R))
    exact IsLocalRing.eq_maximalIdeal this
  haveI hco : IsCO O' (Til O O' R) := UpperTheory.V.Alg.co_mvps O' (O' ⊗[O] R) Unit
  refine ⟨hco, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have hr' : IsUnit (PowerSeries.C ((1 : O') ⊗ₜ[O] r) : PowerSeries (O' ⊗[O] R)) := hr
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at hr'
    exact hloc.map_nonunit r hr'
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    show ¬ IsUnit (PowerSeries.X : PowerSeries (O' ⊗[O] R))
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilEv
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

section
variable {R : Type} [CommRing R] {ι : Type} (N : Type) [AddCommGroup N] [Module R N]

private theorem UpperTheory.V.Pa.BC.ev_nat {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (x : M ⊗[R] (ι → N)) (k : ι) :
    TensorProduct.piRightHom R R M' (fun _ : ι => N) (f.rTensor _ x) k =
      f.rTensor N (TensorProduct.piRightHom R R M (fun _ : ι => N) x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

private theorem UpperTheory.V.Pa.BC.ev_free (n : ℕ) :
    Function.Bijective (TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) := by
  classical
  let e1 : (Fin n → R) ⊗[R] (ι → N) ≃ₗ[R] (Fin n → ι → N) :=
    TensorProduct.piLeft R (ι → N) (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R (ι → N))
  let e2 : (ι → (Fin n → R) ⊗[R] N) ≃ₗ[R] (ι → Fin n → N) :=
    LinearEquiv.piCongrRight (fun _ => TensorProduct.piLeft R N (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R N))
  have key : ∀ x, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) x =
      e2.symm (Equiv.piComm _ (e1 x)) := by
    intro x
    apply e2.injective
    rw [LinearEquiv.apply_symm_apply]
    induction x using TensorProduct.induction_on with
    | zero =>
      ext k i
      simp
      rfl
    | tmul v f =>
      ext k i
      simp [e1, e2, TensorProduct.piRightHom_tmul, Function.swap, LinearEquiv.piCongrRight_apply]
    | add a b ha hb =>
      ext k i
      have h1 := congrFun (congrFun ha k) i
      have h2 := congrFun (congrFun hb k) i
      simp only [map_add (f := _), Pi.add_apply, Equiv.piComm_apply] at h1 h2 ⊢
      rw [h1, h2]
      rfl
  have hfun : ⇑(TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) =
      e2.symm ∘ (Equiv.piComm _) ∘ e1 := funext key
  rw [hfun]
  exact e2.symm.bijective.comp ((Equiv.piComm _).bijective.comp e1.bijective)

private theorem UpperTheory.V.Pa.BC.ev_surj (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  intro z
  choose w hw using fun k => LinearMap.rTensor_surjective N hp (z k)
  obtain ⟨y, hy⟩ := (UpperTheory.V.Pa.BC.ev_free (R := R) (ι := ι) N n).2 w
  refine ⟨p.rTensor _ y, ?_⟩
  funext k
  rw [UpperTheory.V.Pa.BC.ev_nat, hy, hw]

private theorem UpperTheory.V.Pa.BC.ev_bij [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  haveI := Module.finitePresentation_of_finite R M
  refine ⟨?_, UpperTheory.V.Pa.BC.ev_surj N M⟩
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective (ι → N) hf x
  have hex := rTensor_exact N hfg hf
  have hk : ∀ k, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) y k ∈
      Set.range (g.rTensor N) := by
    intro k
    have h1 := congrFun hx k
    rw [UpperTheory.V.Pa.BC.ev_nat, Pi.zero_apply] at h1
    exact (hex _).1 h1
  choose z hz using hk
  obtain ⟨w, hw⟩ := (UpperTheory.V.Pa.BC.ev_free N m).2 z
  have hy : y = g.rTensor _ w := by
    apply (UpperTheory.V.Pa.BC.ev_free N n).1
    funext k
    rw [UpperTheory.V.Pa.BC.ev_nat, hw, hz]
  rw [hy, ← LinearMap.rTensor_comp_apply, hfg.linearMap_comp_eq_zero, LinearMap.rTensor_zero,
    LinearMap.zero_apply]

end

theorem UpperTheory.V.Pa.BC.til_ev :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M] [Module.Finite R M], ∃ e : Til O O' R ⊗[R] M ≃+ (ℕ → O' ⊗[O] M), ∀ a m k, e (a ⊗ₜ m) k = Til.act O' m (Til.coeff O O' R k a) := by
  intro O O' _ _ _ _ R _ _ _ M _ _ _ _ _
  let N := R ⊗[O] O'
  let tc : O' ⊗[O] R ≃ₗ[O] N := TensorProduct.comm O O' R
  have hadd : ∀ (k : ℕ) (a b : Til O O' R),
      Til.coeff O O' R k (a + b) = Til.coeff O O' R k a + Til.coeff O O' R k b := by
    intro k a b
    unfold Til.coeff
    exact map_add (PowerSeries.coeff k) (show PowerSeries (O' ⊗[O] R) from a)
      (show PowerSeries (O' ⊗[O] R) from b)
  have hmulC : ∀ (k : ℕ) (r : R) (a : Til O O' R),
      Til.coeff O O' R k (algebraMap R (Til O O' R) r * a) = ((1 : O') ⊗ₜ[O] r) * Til.coeff O O' R k a := by
    intro k r a
    unfold Til.coeff
    exact PowerSeries.coeff_C_mul k (show PowerSeries (O' ⊗[O] R) from a) ((1 : O') ⊗ₜ[O] r)
  have hsm : ∀ (r : R) (c : O' ⊗[O] R), tc (((1 : O') ⊗ₜ[O] r) * c) = r • tc c := by
    intro r c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp only [tc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => rw [mul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]
  let cf : Til O O' R →ₗ[R] (ℕ → N) :=
    { toFun := fun a k => tc (Til.coeff O O' R k a)
      map_add' := fun a b => by
        funext k
        simp only [hadd, map_add (f := _), Pi.add_apply]
      map_smul' := fun r a => by
        funext k
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [Algebra.smul_def, hmulC, hsm] }
  have hcf : Function.Bijective cf := by
    constructor
    · intro a b hab
      apply PowerSeries.ext
      intro k
      have h1 := congrFun hab k
      exact tc.injective h1
    · intro f
      refine ⟨PowerSeries.mk (fun k => tc.symm (f k)), ?_⟩
      funext k
      change tc (PowerSeries.coeff k (PowerSeries.mk (fun k => tc.symm (f k)))) = f k
      rw [PowerSeries.coeff_mk, LinearEquiv.apply_symm_apply]
  let cfe : Til O O' R ≃ₗ[R] (ℕ → N) := LinearEquiv.ofBijective cf hcf
  have hev := UpperTheory.V.Pa.BC.ev_bij (R := R) (ι := ℕ) N M
  let eve : M ⊗[R] (ℕ → N) ≃ₗ[R] (ℕ → M ⊗[R] N) :=
    LinearEquiv.ofBijective (TensorProduct.piRightHom R R M (fun _ : ℕ => N)) hev
  let cb : M ⊗[R] N ≃+ O' ⊗[O] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange O R R M O').toAddEquiv.trans
      (TensorProduct.comm O M O').toAddEquiv
  have hcb : ∀ (m : M) (c : O' ⊗[O] R), cb (m ⊗ₜ[R] tc c) = Til.act O' m c := by
    intro m c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp [cb, tc, Til.act, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      rw [TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.comm_tmul]
    | add x y hx hy => rw [map_add (f := _), TensorProduct.tmul_add, map_add (f := _), hx, hy, map_add (f := _)]
  refine ⟨(TensorProduct.comm R (Til O O' R) M).toAddEquiv.trans
    ((cfe.lTensor M).toAddEquiv.trans (eve.toAddEquiv.trans (AddEquiv.piCongrRight (fun _ => cb)))), ?_⟩
  intro a m k
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, TensorProduct.comm_tmul,
    LinearEquiv.lTensor_tmul, AddEquiv.piCongrRight_apply]
  rw [← hcb]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilQuot
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem mem_map_C_of_forall_coeff_mem_of_fg {A : Type} [CommRing A] (J : Ideal A) (hJ : J.FG) (f : PowerSeries A)
    (h : ∀ n, PowerSeries.coeff n f ∈ J) : f ∈ J.map PowerSeries.C := by
  obtain ⟨s, rfl⟩ := hJ
  have hc : ∀ n, ∃ c : A → A, Function.support c ⊆ ↑s ∧ ∑ a ∈ s, c a • a = PowerSeries.coeff n f :=
    fun n => Submodule.mem_span_finset.mp (h n)
  choose c _ hc using hc
  have hf : f = ∑ a ∈ s, PowerSeries.C a * PowerSeries.mk (fun n => c n a) := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    rw [← hc n]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hf]
  refine Ideal.sum_mem _ fun a ha => Ideal.mul_mem_right _ _ ?_
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ha)

theorem UpperTheory.V.Pa.BC.til_quot :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (R : Type) [CommRing R] [Algebra O R] (I : Ideal R), I.FG → Function.Surjective (Til.map O' (Ideal.Quotient.mkₐ O I)) ∧ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I)) = I.map (Til.ι O O' R) := by
  intro O O' _ _ _ R _ _ I hI
  set φ := Algebra.TensorProduct.map (AlgHom.id O' O') (Ideal.Quotient.mkₐ O I) with hφ
  have hsurj : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩) (Ideal.Quotient.mkₐ_surjective O I)
  have hker : RingHom.ker φ = I.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) := by
    have e := Algebra.TensorProduct.lTensor_ker (A := O') (Ideal.Quotient.mkₐ O I)
      (Ideal.Quotient.mkₐ_surjective O I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ O I) = I := by
      ext x
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hk] at e
    rw [← e]
    rfl
  have hcoeff : ∀ (f : Til O O' R) (n : ℕ),
      PowerSeries.coeff n (Til.map O' (Ideal.Quotient.mkₐ O I) f : PowerSeries (O' ⊗[O] (R ⧸ I)))
        = φ (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R))) :=
    fun f n => PowerSeries.coeff_map _ _ _
  refine ⟨?_, ?_⟩
  · intro f
    refine ⟨(PowerSeries.mk fun n =>
      (hsurj (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] (R ⧸ I))))).choose : PowerSeries (O' ⊗[O] R)), ?_⟩
    apply PowerSeries.ext
    intro n
    refine (hcoeff _ n).trans ?_
    erw [PowerSeries.coeff_mk]
    exact (hsurj _).choose_spec
  · have hι : I.map (Til.ι O O' R) = (RingHom.ker φ).map (Til.C O O' R) := by
      rw [hker]
      exact (Ideal.map_map _ _).symm
    rw [hι]
    ext f
    rw [RingHom.mem_ker]
    constructor
    · intro hf
      have h : ∀ n, PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R)) ∈ RingHom.ker φ := by
        intro n
        rw [RingHom.mem_ker, ← hcoeff, hf]
        exact map_zero _
      have hJ : (RingHom.ker φ).FG := by
        rw [hker]
        exact hI.map _
      exact mem_map_C_of_forall_coeff_mem_of_fg _ hJ f h
    · intro hf
      refine (Ideal.map_le_iff_le_comap.mpr ?_ : (RingHom.ker φ).map (Til.C O O' R)
        ≤ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I))) hf
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      apply PowerSeries.ext
      intro n
      rw [hcoeff]
      change φ (PowerSeries.coeff n (PowerSeries.C x : PowerSeries (O' ⊗[O] R)))
        = PowerSeries.coeff n (0 : PowerSeries (O' ⊗[O] (R ⧸ I)))
      rw [PowerSeries.coeff_C, map_zero]
      split_ifs
      · exact RingHom.mem_ker.mp hx
      · exact map_zero _
end

