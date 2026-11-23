module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LinAlg
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem finrank_quotient_le_of_forall_dependent_mod {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]
    (g : ℕ) (U : Submodule F V)
    (h : ∀ z : Fin (g + 1) → V, ∃ c : Fin (g + 1) → F, c ≠ 0 ∧ ∑ i, c i • z i ∈ U) :
    Module.finrank F (V ⧸ U) ≤ g := by
  by_contra hlt
  push_neg at hlt
  let b := Module.finBasis F (V ⧸ U)
  let y : Fin (g + 1) → V ⧸ U := fun i => b (Fin.castLE hlt i)
  have hli : LinearIndependent F y := b.linearIndependent.comp _ (Fin.castLE_injective hlt)
  choose z hz using fun i => U.mkQ_surjective (y i)
  obtain ⟨c, hc0, hc⟩ := h z
  have hsum : ∑ i, c i • y i = 0 := by
    have : U.mkQ (∑ i, c i • z i) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hc
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_smul, hz] using this
  exact hc0 (funext fun i => Fintype.linearIndependent_iff.1 hli c hsum i)

private theorem exists_spanning_family_of_finrank_le {F V : Type} [Field F] [AddCommGroup V] [Module F V] (N : ℕ)
    (C : Submodule F V) [Module.Finite F C] (h : Module.finrank F C ≤ N) :
    ∃ ψ : Fin N → V, (∀ i, ψ i ∈ C) ∧ C ≤ Submodule.span F (Set.range ψ) := by
  classical
  let b := Module.finBasis F C
  refine ⟨fun i => if hi : (i : ℕ) < Module.finrank F C then (b ⟨i, hi⟩ : V) else 0, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact (b _).2
    · exact C.zero_mem
  · intro f hf
    have hf' : f = ∑ k, b.repr ⟨f, hf⟩ k • (b k : V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨f, hf⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hf']
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨k, lt_of_lt_of_le k.2 h⟩, ?_⟩)
    simp [k.2]

theorem UpperTheory.V.Pa.linAlg :
    ∀ (F T : Type) [Field F] [AddCommGroup T] [Module F T] [Module.Finite F T] (g D0 : ℕ) (U : Submodule F (Fin g → T)), (∀ z : Fin (g + 1) → Fin g → T, ∃ c : Fin (g + 1) → F, c ≠ 0 ∧ ∑ i, c i • z i ∈ U) → (∀ (e : ℕ) (α : Fin e → T), LinearIndependent F α → (∀ i j, Pi.single j (α i) ∈ U) → e + g * g ≤ D0) → ∃ (X : Fin D0 → Module.Dual F T) (c : Fin g × Fin g → Fin D0 → F), Submodule.span F (Set.range X) = ⊤ ∧ LinearIndependent F c ∧ ∀ a ∈ U, ∀ i, ∑ j, ∑ k, c (i, j) k * X k (a j) = 0 := by
  intro F T _ _ _ _ g D0 U h1 h2
  classical
  have hAdim : Module.finrank F U.dualAnnihilator ≤ g := by
    have e1 := finrank_quotient_le_of_forall_dependent_mod g U h1
    have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq U
    have e3 := Submodule.finrank_quotient_add_finrank U
    omega
  obtain ⟨Φ, hΦA, hΦspan⟩ := exists_spanning_family_of_finrank_le g U.dualAnnihilator hAdim
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin g → Fin g → Module.Dual F T, ∀ i j t, φ i j t = Φ i (Pi.single j t) :=
    ⟨fun i j => (Φ i).comp (LinearMap.single F (fun _ : Fin g => T) j), fun i j t => rfl⟩
  have hrow : ∀ a ∈ U, ∀ i, ∑ j, φ i j (a j) = 0 := by
    intro a ha i
    simp only [hφ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Finset.univ_sum_single]
    exact (Submodule.mem_dualAnnihilator _).1 (hΦA i) a ha
  set W : Submodule F T := ⨅ j : Fin g, U.comap (LinearMap.single F (fun _ : Fin g => T) j) with hWdef
  have hW : Module.finrank F W + g * g ≤ D0 := by
    let bW := Module.finBasis F W
    refine h2 _ (fun k => (bW k : T)) ?_ ?_
    · exact bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    · intro k j
      have hmem : (bW k : T) ∈ ⨅ j : Fin g, U.comap (LinearMap.single F (fun _ : Fin g => T) j) :=
        (bW k).2
      rw [Submodule.mem_iInf] at hmem
      exact hmem j
  set S : Submodule F (Module.Dual F T) :=
    Submodule.span F (Set.range fun p : Fin g × Fin g => φ p.1 p.2) with hSdef
  have hSco : S.dualCoannihilator ≤ W := by
    intro t ht
    rw [Submodule.mem_dualCoannihilator] at ht
    rw [hWdef, Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_comap, ← Subspace.dualAnnihilator_dualCoannihilator_eq (W := U),
      Submodule.mem_dualCoannihilator]
    intro f hf
    have hle : Submodule.span F (Set.range Φ) ≤ LinearMap.ker
        (Module.Dual.eval F (Fin g → T) (LinearMap.single F (fun _ : Fin g => T) j t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      have := ht _ (Submodule.subset_span ⟨(i, j), rfl⟩)
      simpa [hφ] using this
    have := hle (hΦspan hf)
    simpa using this
  have hSrank : Module.finrank F T ≤ Module.finrank F S + Module.finrank F W := by
    have e1 := Subspace.finrank_add_finrank_dualCoannihilator_eq S
    have e2 := Submodule.finrank_mono hSco
    omega
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  have hCdim : Module.finrank F C ≤ D0 - g * g := by
    have e1 := Submodule.finrank_add_eq_of_isCompl hC
    have e2 : Module.finrank F (Module.Dual F T) = Module.finrank F T := Subspace.dual_finrank_eq
    omega
  obtain ⟨ψ, -, hψspan⟩ := exists_spanning_family_of_finrank_le (D0 - g * g) C hCdim
  have hgD : g * g ≤ D0 := le_trans (Nat.le_add_left _ _) hW
  let e : Fin D0 ≃ Fin (g * g) ⊕ Fin (D0 - g * g) := (finCongr (by omega)).trans finSumFinEquiv.symm
  let κ : Fin g × Fin g → Fin D0 := fun p => e.symm (Sum.inl (finProdFinEquiv p))
  have hκ : Function.Injective κ := fun p q hpq =>
    finProdFinEquiv.injective (Sum.inl_injective (e.symm.injective hpq))
  let X : Fin D0 → Module.Dual F T := fun k =>
    Sum.elim (fun m => φ (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2) ψ (e k)
  have hXκ : ∀ p, X (κ p) = φ p.1 p.2 := by
    intro p
    simp only [X, κ, Equiv.apply_symm_apply, Sum.elim_inl, Equiv.symm_apply_apply]
  refine ⟨X, fun p => Pi.basisFun F (Fin D0) (κ p), ?_,
    (Pi.basisFun F (Fin D0)).linearIndependent.comp κ hκ, ?_⟩
  · rw [eq_top_iff, ← hC.sup_eq_top, sup_le_iff]
    constructor
    · rw [hSdef, Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span ⟨κ p, by simp only [hXκ]⟩
    · refine le_trans hψspan (Submodule.span_mono ?_)
      rintro _ ⟨m, rfl⟩
      refine ⟨e.symm (Sum.inr m), ?_⟩
      simp only [X, Equiv.apply_symm_apply, Sum.elim_inr]
  · intro a ha i
    rw [← hrow a ha i]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.basisFun_apply, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hXκ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OoExKer
section
@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ooEx_co (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) : IsCO O K := by
  refine { complete := ?_, isLocalHom := ?_, res_surj := ?_ }
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal a).mpr hna
    have hk : RingHom.ker (algebraMap O K) = maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ h)
    rw [← hk, RingHom.mem_ker] at hm
    rw [hm] at ha
    exact not_isUnit_zero ha
  · intro x
    obtain ⟨a, rfl⟩ := h x
    exact ⟨a, by simp⟩

private theorem ooEx_ker (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) (π : O) (hπ : maximalIdeal O = Ideal.span {π}) :
    RingHom.ker (PowerSeries.map (algebraMap O K)) = Ideal.span {PowerSeries.C π} := by
  have hk : RingHom.ker (algebraMap O K) = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ h)
  have hπ0 : algebraMap O K π = 0 := by
    rw [← RingHom.mem_ker, hk, hπ]
    exact Ideal.mem_span_singleton_self π
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have hc : ∀ n, ∃ c, PowerSeries.coeff n x = π * c := by
      intro n
      have h1 : algebraMap O K (PowerSeries.coeff n x) = 0 := by
        have := congrArg (PowerSeries.coeff n) hx
        simpa using this
      have h2 : PowerSeries.coeff n x ∈ maximalIdeal O := by
        rw [← hk, RingHom.mem_ker]
        exact h1
      rw [hπ, Ideal.mem_span_singleton] at h2
      exact h2
    choose c hc using hc
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    simp [PowerSeries.coeff_C_mul, hc]
  · rintro ⟨y, rfl⟩
    rw [map_mul, PowerSeries.map_C, hπ0, map_zero, zero_mul]

private theorem ooEx_ev (K O B : Type) [Field K] [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra O K] [CommRing B] [Algebra O B] [IsCO O B]
    (f : B →ₐ[O] PowerSeries K) (s : B) (h : Function.Surjective (algebraMap O K)) (hs : f s = PowerSeries.X) :
    ∃ F : PowerSeries O →+* B, (∀ c : O, F (PowerSeries.C c) = algebraMap O B c) ∧ F PowerSeries.X = s ∧
      ∀ x, f (F x) = PowerSeries.map (algebraMap O K) x := by
  haveI hOO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun a h => by simpa using h⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hK : IsCO O K := ooEx_co O K h
  haveI hPK : IsCO O (MvPowerSeries Unit K) := co_mvps O K Unit
  have hsm : s ∈ maximalIdeal B := by
    by_contra hns
    have hu : IsUnit s := by
      by_contra h'
      exact hns ((IsLocalRing.mem_maximalIdeal s).mpr h')
    have hX : IsUnit (PowerSeries.X : PowerSeries K) := hs ▸ hu.map f
    rw [PowerSeries.isUnit_iff_constantCoeff] at hX
    simp at hX
  obtain ⟨G, ⟨hGC, hGX⟩, -⟩ := co_ev O O B Unit (Algebra.ofId O B) (fun _ => s) (fun _ => hsm)
  refine ⟨G.toRingHom, ?_, ?_, ?_⟩
  · intro c
    exact hGC c
  · exact hGX ()
  · let M : MvPowerSeries Unit O →ₐ[O] MvPowerSeries Unit K :=
      { MvPowerSeries.map (algebraMap O K) with
        commutes' := fun c => by
          simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
          exact MvPowerSeries.map_C _ _ }
    have hXm : MvPowerSeries.X () ∈ maximalIdeal (MvPowerSeries Unit K) := by
      refine (IsLocalRing.mem_maximalIdeal _).mpr ?_
      intro hu
      rw [MvPowerSeries.isUnit_iff_constantCoeff] at hu
      simp at hu
    obtain ⟨H, -, hU⟩ := co_ev O O (MvPowerSeries Unit K) Unit (Algebra.ofId O _)
      (fun _ => MvPowerSeries.X ()) (fun _ => hXm)
    have e1 : (f.comp G : MvPowerSeries Unit O →ₐ[O] MvPowerSeries Unit K) = H := by
      refine hU _ ⟨fun x => ?_, fun u => ?_⟩
      · simp [hGC]
      · simp only [AlgHom.comp_apply, hGX, hs]
        rfl
    have e2 : M = H := by
      refine hU _ ⟨fun x => ?_, fun u => ?_⟩
      · simp [M, MvPowerSeries.algebraMap_apply]
      · simp [M]
    intro x
    have := congrArg (fun φ : MvPowerSeries Unit O →ₐ[O] MvPowerSeries Unit K => φ x) (e1.trans e2.symm)
    exact this

theorem UpperTheory.V.Pa.ooEx :
    ∀ (K O B Bh : Type) [Field K] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite K] [Algebra O K] [CommRing B] [Algebra O B] [IsCO O B] [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (f : B →ₐ[O] PowerSeries K) (s : B) (rF : Bh →+* FractionRing (PowerSeries K)), Function.Surjective (algebraMap O K) → f s = PowerSeries.X → IsCplAt B (RingHom.ker f) Bh → (∀ b, rF (algebraMap B Bh b) = algebraMap (PowerSeries K) _ (f b)) → ∃ (OO : Type) (_ : CommRing OO) (_ : IsDomain OO) (_ : IsDiscreteValuationRing OO) (_ : IsAdicComplete (maximalIdeal OO) OO) (_ : Algebra OO Bh) (_ : IsCO OO Bh), (∀ a : PowerSeries K, ∃ (o : OO) (b : B), algebraMap OO Bh o = algebraMap B Bh b ∧ f b = a) ∧ (∀ c : O, ∃ o : OO, algebraMap OO Bh o = algebraMap B Bh (algebraMap O B c)) ∧ (∃ o : OO, algebraMap OO Bh o = algebraMap B Bh s) ∧ Function.Surjective (rF.comp (algebraMap OO Bh)) := by
  intro K O B Bh _ _ _ _ _ _ _ _ _ _ _ _ _ f s rF hsur hs hcpl hrF
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ := hπirr.maximalIdeal_eq
  obtain ⟨F, hFC, hFX, hfF⟩ := ooEx_ev K O B f s hsur hs
  have hker := ooEx_ker O K hsur π hπ
  have hmapsurj : Function.Surjective (PowerSeries.map (algebraMap O K)) := by
    intro a
    choose g hg using hsur
    refine ⟨PowerSeries.mk (fun n => g (PowerSeries.coeff n a)), ?_⟩
    ext n
    simp [hg]
  obtain ⟨p, hp⟩ : ∃ p : Ideal (PowerSeries O), p = Ideal.span {PowerSeries.C π} := ⟨_, rfl⟩
  rw [← hp] at hker
  haveI hpP : p.IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime _
  have hπ0 : PowerSeries.C π ≠ 0 := by
    intro h0
    apply hπirr.ne_zero
    have := congrArg PowerSeries.constantCoeff h0
    simpa using this
  have hprime : Prime (PowerSeries.C π) := (Ideal.span_singleton_prime hπ0).mp (hp ▸ hpP)
  have hcO : IsCplAt (PowerSeries O) p (CplAt (PowerSeries O) p) := isCplAt_cplAt _ p
  obtain ⟨hdom, hdvr, -⟩ := IsCplAt.dvr (PowerSeries O) (PowerSeries.C π) hprime
    (CplAt (PowerSeries O) p) (hp ▸ hcO)
  let φ : PowerSeries O →+* Bh := (algebraMap B Bh).comp F
  have hcomapF : Ideal.comap F (RingHom.ker f) = p := by
    rw [← hker]
    ext x
    simp only [Ideal.mem_comap, RingHom.mem_ker, hfF]
  have hφ : Ideal.comap φ (maximalIdeal Bh) = p := by
    rw [← Ideal.comap_comap, hcpl.comap_eq, hcomapF]
  haveI := hcpl.complete
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift (PowerSeries O) p (CplAt (PowerSeries O) p) hcO Bh φ hφ
  letI : Algebra (CplAt (PowerSeries O) p) Bh := ψ.toAlgebra
  letI : Algebra (PowerSeries O) B := F.toAlgebra
  letI : Algebra (PowerSeries O) Bh := φ.toAlgebra
  haveI : IsScalarTower (PowerSeries O) B Bh := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower (PowerSeries O) (CplAt (PowerSeries O) p) Bh :=
    IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun hψ x).symm)
  have hCO : IsCO (CplAt (PowerSeries O) p) Bh := by
    refine IsCplAt.isCO (PowerSeries O) B p (RingHom.ker f) (CplAt (PowerSeries O) p) Bh hcO hcpl ?_ ?_
    · exact hcomapF
    · intro x
      obtain ⟨a, ha⟩ := hmapsurj (f x)
      refine ⟨a, ?_⟩
      rw [RingHom.mem_ker, map_sub]
      show f x - f (F a) = 0
      rw [hfF, ha, sub_self]
  have hkey : ∀ c, rF (ψ (algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) c)) =
      algebraMap (PowerSeries K) _ (PowerSeries.map (algebraMap O K) c) := by
    intro c
    have h1 := RingHom.congr_fun hψ c
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    show rF (algebraMap B Bh (F c)) = _
    rw [hrF, hfF]
  refine ⟨CplAt (PowerSeries O) p, inferInstance, hdom, hdvr, hcO.complete, inferInstance, hCO, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨c, hc⟩ := hmapsurj a
    exact ⟨algebraMap _ (CplAt (PowerSeries O) p) c, F c, RingHom.congr_fun hψ c, by rw [hfF, hc]⟩
  · intro c
    refine ⟨algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) (PowerSeries.C c), ?_⟩
    refine (RingHom.congr_fun hψ _).trans ?_
    show algebraMap B Bh (F (PowerSeries.C c)) = _
    rw [hFC]
  · refine ⟨algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) PowerSeries.X, ?_⟩
    refine (RingHom.congr_fun hψ _).trans ?_
    show algebraMap B Bh (F PowerSeries.X) = _
    rw [hFX]
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (PowerSeries K) z
    obtain ⟨cx, hcx⟩ := hmapsurj x
    obtain ⟨cy, hcy⟩ := hmapsurj y
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hcyp : cy ∉ p := by
      rw [← hker, RingHom.mem_ker, hcy]
      exact hy0
    have hunit : IsUnit (algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) cy) := by
      by_contra hu
      apply hcyp
      rw [← hcO.comap_eq, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hu
    obtain ⟨u, hu⟩ := hunit
    refine ⟨algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) cx * ↑u⁻¹, ?_⟩
    rw [map_mul, map_units_inv, RingHom.comp_apply, RingHom.comp_apply]
    show rF (ψ (algebraMap _ (CplAt (PowerSeries O) p) cx)) * (rF (ψ ↑u))⁻¹ = _
    rw [hu, hkey, hkey, hcx, hcy, div_eq_mul_inv]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prAdd :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a) ∧ (∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧ S.pr1 (algebraMap S.Bh S.U.AA b + y) = y) ∧ (∀ a a', S.pr0 (a + a') = S.pr0 a + S.pr0 a' ∧ S.pr1 (a + a') = S.pr1 a + S.pr1 a') ∧ (∀ (b : S.Bh) a, S.pr0 (b • a) = b * S.pr0 a ∧ S.pr1 (b • a) = b • S.pr1 a) ∧ (∀ a a', S.pr0 (a * a') - S.pr0 a * S.pr0 a' ∈ ired S.U.N ∧ S.pr1 (a * a') = S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) ∧ ired S.U.N ≤ maximalIdeal S.Bh ∧ S.J2 ≤ maximalIdeal S.Bh := by
  intro l _ S
  have h1 : ∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a := by
    intro a
    simp [Ctx.pr1]
  have h2 : ∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧
      S.pr1 (algebraMap S.Bh S.U.AA b + y) = y := by
    intro b y
    have e := h1 (algebraMap S.Bh S.U.AA b + y)
    have hm : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) ∈ S.U.N := by
      have : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) =
          (y : S.U.AA) - (S.pr1 (algebraMap S.Bh S.U.AA b + y) : S.U.AA) := by
        rw [map_sub]; linear_combination e
      rw [this]
      exact S.U.N.sub_mem y.2 (S.pr1 _).2
    have hz : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) = 0 :=
      Submodule.disjoint_def.1 S.U.compl.disjoint _ (Submodule.mem_one.2 ⟨_, rfl⟩) hm
    have hb : S.pr0 (algebraMap S.Bh S.U.AA b + y) = b :=
      sub_eq_zero.1 (S.U.inj (by rw [hz, map_zero]))
    refine ⟨hb, Subtype.ext ?_⟩
    rw [hb] at e
    exact add_left_cancel e
  have key : ∀ (a : S.U.AA) (b : S.Bh) (y : S.U.N), a = algebraMap S.Bh S.U.AA b + y →
      S.pr0 a = b ∧ S.pr1 a = y := by
    rintro a b y rfl
    exact h2 b y
  have hi : ired S.U.N ≤ maximalIdeal S.Bh := by
    refine Ideal.span_le.2 ?_
    rintro b ⟨x, hx, y, hy, e⟩
    obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx y hy
    have : b = c := S.U.inj (e.symm.trans e')
    rw [this]; exact hc
  refine ⟨h1, h2, fun a a' => key _ _ _ ?_, fun b a => key _ _ _ ?_, fun a a' => ?_, hi, ?_⟩
  · rw [map_add (f := _), Submodule.coe_add]
    linear_combination - h1 a - h1 a'
  · rw [map_mul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def, ← mul_add, h1]
  · obtain ⟨c, -, e⟩ := S.U.mul_mem _ (S.pr1 a).2 _ (S.pr1 a').2
    have := key (a * a') (S.pr0 a * S.pr0 a' + c) (S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) (by
      rw [map_add (f := _), map_mul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def,
        Algebra.smul_def, ← e]
      have e1 := h1 a
      have e2 := h1 a'
      linear_combination (- a') * e1 - (algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA)) * e2)
    refine ⟨?_, this.2⟩
    rw [this.1, add_sub_cancel_left]
    exact Ideal.subset_span ⟨_, (S.pr1 a).2, _, (S.pr1 a').2, e⟩
  · refine sup_le (sup_le ?_ (Ideal.pow_le_self two_ne_zero)) hi
    exact ((IsLocalRing.local_hom_tfae (algebraMap S.OO S.Bh)).out 1 3).1 (IsCO.isLocalHom (O := S.OO) (R := S.Bh))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrVr
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prVr :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ g (i j : Fin S.n), S.rF (S.pr0 (S.U.vr g i j)) = S.ρ S.F g i j ∧ ((((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr1 (S.U.vr g i j) = 0) ∧ (¬ (((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr0 (S.U.vr g i j) = 0) := by
  intro l _ S g i j
  have hm : S.U.vr g ∈ blkMat S.n S.x.a (1 : Submodule S.Bh S.U.AA) S.U.N := by
    rw [← S.U.span]; exact Submodule.subset_span ⟨g, rfl⟩
  have hN : S.U.vr g i j - algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ S.U.N := (S.pr1 (S.U.vr g i j)).2
  have hd := Submodule.disjoint_def.1 S.U.compl.disjoint
  have h1 : algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ (1 : Submodule S.Bh S.U.AA) :=
    Submodule.mem_one.2 ⟨_, rfl⟩
  refine ⟨S.U.red g i j _ hN, fun e => ?_, fun e => ?_⟩
  · exact Subtype.ext (hd _ (Submodule.sub_mem _ ((hm i j).1 e) h1) hN)
  · apply S.U.inj
    rw [map_zero]
    refine hd _ h1 ?_
    have := S.U.N.sub_mem ((hm i j).2 e) hN
    rwa [sub_sub_cancel] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PresOut0
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.presOut0 :
    ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] (D0 : ℕ) (X : Fin D0 → B), (∀ a, X a ∈ maximalIdeal B) → maximalIdeal B ≤ Ideal.span (Set.range X) ⊔ ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2) → ∀ Z Q : Ideal B, Z.IsPrime → Q.IsPrime → ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Z) → Z ≤ Q := by
  intro O B _ _ _ _ _ _ _ D0 X hX hspan Z Q hZ hQ hdim
  haveI hOO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun a h => by simpa using h⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hA : IsCO O (MvPowerSeries (Fin D0) O) := co_mvps O O (Fin D0)
  obtain ⟨F, ⟨hFC, hFX⟩, -⟩ := co_ev O O B (Fin D0) (Algebra.ofId O B) X hX
  have hsurj : Function.Surjective F := by
    apply co_surj
    refine le_trans hspan (sup_le ?_ (sup_le ?_ le_sup_right))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.mem_sup_left ?_
      rw [← hFX i]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simp
    · refine le_sup_of_le_left ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h1 : algebraMap O B a = F (MvPowerSeries.C a) := by
        rw [hFC]; rfl
      rw [h1]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simpa using ha
  have hdimA : ringKrullDim (MvPowerSeries (Fin D0) O) = 1 + (D0 : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp
  have hinj : ∀ r, F r ∈ Z → r = 0 := by
    intro r hr
    by_contra hne
    have hnz : r ∈ nonZeroDivisors (MvPowerSeries (Fin D0) O) := mem_nonZeroDivisors_of_ne_zero hne
    have hle := ringKrullDim_succ_le_of_surjective ((Ideal.Quotient.mk Z).comp F.toRingHom)
      ((Ideal.Quotient.mk_surjective).comp hsurj) hnz (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hr)
    rw [hdimA] at hle
    generalize ringKrullDim (B ⧸ Z) = d at hle hdim
    have hb : d ≠ ⊥ := ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) hdim
    obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hb
    have h2 : (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) := hdim
    rw [WithBot.coe_le_coe] at h2
    have h1 : ((e + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast at hle ⊢; exact hle
    rw [WithBot.coe_le_coe] at h1
    have het : e ≠ ⊤ := by
      intro h; rw [h] at h1; simp at h1
    lift e to ℕ using het
    norm_cast at h1 h2
    omega
  have hZbot : Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨r, rfl⟩ := hsurj z
    rw [hinj r hz, map_zero]
    exact Ideal.zero_mem _
  rw [hZbot]
  exact bot_le
end

