module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0014
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLocallyConstantDOneEqCocycleOfTameInertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

section SlopeTestRemainingChoices

open Formalism.GaloisCohomology UpperTheory.V.Base

private theorem dz_locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem dz_exists_prime {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (hn : n ≠ 0) (h : (n : 𝓞 F) ∈ v.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : 𝓞 F) ∈ v.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk5.dz_exists_prime v n hn h

private theorem dz_not_both {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a b : ℕ} (hab : a.Coprime b) (ha : (a : 𝓞 F) ∈ v.asIdeal)
    (hb : (b : 𝓞 F) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, h⟩ : IsCoprime (a : 𝓞 F) (b : 𝓞 F) := hab.cast
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ha) (v.asIdeal.mul_mem_left _ hb)))

private theorem dz_val {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ ((n : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have h := hv ((n : ℕ) : 𝓞 F)
  have e : algebraMap F Ω (((n : ℕ) : 𝓞 F) : F) = (n : Ω) := by simp
  rw [e] at h
  exact h

private theorem dz_order {q n m : ℕ} (hq : 1 < q) (hn : 0 < n) (hm : m + 1 = q ^ n) (u : (ZMod m)ˣ)
    (hu : (u : ZMod m) = q) : orderOf u = n := by
  rw [orderOf_eq_iff hn]
  refine ⟨Units.ext ?_, fun k hk hk0 h => ?_⟩
  · rw [Units.val_pow_eq_pow_val, hu, ← Nat.cast_pow, ← hm]
    simp
  · have h1 : ((q ^ k : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
      rw [Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h]
      simp
    have h2 : 1 < q ^ k := Nat.one_lt_pow hk0.ne' hq
    have h3 : q ^ k < q ^ n := Nat.pow_lt_pow_right hq hk
    have h4 := (Nat.modEq_iff_dvd' h2.le).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).symm
    have h5 := Nat.le_of_dvd (by omega) h4
    omega

private theorem dz_frob (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F))
    (hv : IsPlaceOver A v) (D I : Subgroup (G F Ω)) (hD : D = Dec (F := F) A) (hI : I = Ine (F := F) A) :
    ∃ φ : D, IsFrob (F := F) A (normV v) φ.1 ∧ (I.subgroupOf D ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧
      ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I.subgroupOf D, d s = 1) ∧
        d φ = Multiplicative.ofAdd 1 := by
  subst hD hI
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  obtain ⟨γ, hγ⟩ := exists_isFrob hv
  refine ⟨⟨γ, hγ.1⟩, hγ, ?_, fun n hn => ?_⟩
  · have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G F Ω)
      ⟨(Ine (F := F) A ⊔ Subgroup.zpowers γ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
    have h1 : Dec (F := F) A ≤ (Ine (F := F) A ⊔ Subgroup.zpowers γ).topologicalClosure := by
      refine le_trans (le_sInf ?_) key.ge
      rintro N ⟨hNo, hN⟩
      have h := (Subgroup.le_topologicalClosure _).trans hN
      exact Kum.decGen F Ω A _ γ N hv hγ hNo (le_sup_left.trans h)
        (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers γ)))
    have h2 : ((Ine (F := F) A).subgroupOf (Dec (F := F) A) ⊔
        Subgroup.zpowers (⟨γ, hγ.1⟩ : Dec (F := F) A)).map (Dec (F := F) A).subtype =
        Ine (F := F) A ⊔ Subgroup.zpowers γ := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers, inf_eq_left.2 (Ine_le_Dec A)]
      rfl
    rw [eq_top_iff]
    intro x _
    have h3 := h1 x.2
    rw [← h2] at h3
    exact closure_subtype.2 h3
  · have hq : normV v = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    have hq1 : 1 < normV v := by
      rw [hq]
      have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
      have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      omega
    have hqv : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := hq ▸ Ideal.absNorm_mem _
    obtain ⟨p, hp, hpq, hpv⟩ := dz_exists_prime v _ (by omega) hqv
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : 1 < normV v ^ n := Nat.one_lt_pow hn.ne' hq1
    obtain ⟨m, hm⟩ : ∃ m, m + 1 = normV v ^ n := ⟨normV v ^ n - 1, by omega⟩
    haveI : NeZero m := ⟨by omega⟩
    have hmp : m.Coprime p := by
      refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_).symm
      have h2 : p ∣ m + 1 := hm ▸ hpq.trans (dvd_pow_self _ hn.ne')
      exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
    have hA := (dz_val hv p).2 hpv
    obtain ⟨hopen, -, -, -, hIne⟩ := Chr.clsFacts F Ω m
    have hI := hIne A fun h => dz_not_both v hmp ((dz_val hv m).1 h) hpv
    have hu : ((Chr.cls F Ω m γ : (ZMod m)ˣ) : ZMod m) = normV v := by
      haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
      have hv1 : A.valuation ζ ≤ 1 := by
        have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
        exact ((pow_eq_one_iff_left (NeZero.ne m)).1 h1).le
      have h2 : γ ζ = ζ ^ normV v := by
        refine (LDataCardLeFinrank.ineFixRoots F Ω p A hA m hmp (ζ ^ normV v) ?_).1 (γ ζ) ?_ (hγ.2 ζ hv1)
        · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
        · rw [← map_pow, hζ.pow_eq_one, map_one]
      rw [Chr.cls_spec m γ ζ hζ.pow_eq_one, pow_eq_pow_mod (normV v) hζ.pow_eq_one] at h2
      have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos m)) h2
      rw [← ZMod.natCast_zmod_val ((Chr.cls F Ω m γ : (ZMod m)ˣ) : ZMod m), h3, ZMod.natCast_mod]
    have hord := dz_order hq1 hn hm _ hu
    have hle : Dec (F := F) A ≤ (Subgroup.zpowers (Chr.cls F Ω m γ)).comap (Chr.cls F Ω m) := by
      have hk : (Chr.cls F Ω m).ker ≤ (Subgroup.zpowers (Chr.cls F Ω m γ)).comap (Chr.cls F Ω m) :=
        Subgroup.ker_le_comap _ _
      exact Kum.decGen F Ω A _ γ _ hv hγ (Subgroup.isOpen_mono hk hopen) (hI.trans hk) (Subgroup.mem_zpowers _)
    let f : Dec (F := F) A →* Subgroup.zpowers (Chr.cls F Ω m γ) :=
      ((Chr.cls F Ω m).comp (Dec (F := F) A).subtype).codRestrict _ fun x => hle x.2
    have hg : ∀ x : Subgroup.zpowers (Chr.cls F Ω m γ), x ∈ Subgroup.zpowers (f ⟨γ, hγ.1⟩) := by
      rintro ⟨_, k, rfl⟩
      exact ⟨k, rfl⟩
    have hc : Nat.card (Subgroup.zpowers (Chr.cls F Ω m γ)) = n := by rw [Nat.card_zpowers, hord]
    have hf1 : ∀ s : Dec (F := F) A, Chr.cls F Ω m s = 1 → f s = 1 := fun s hs => Subtype.ext hs
    refine ⟨(zmodMulEquivOfGenerator hg hc).symm.toMonoidHom.comp f, dz_locConst _ ?_, fun s hs => ?_, ?_⟩
    · refine Subgroup.isOpen_mono (H₁ := (Chr.cls F Ω m).ker.subgroupOf _) (fun s hs => ?_)
        (hopen.preimage continuous_subtype_val)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf1 s hs, map_one]
    · rw [MonoidHom.comp_apply, hf1 s (hI hs), map_one]
    · exact zmodMulEquivOfGenerator_symm_apply_generator hg hc

end SlopeTestRemainingChoices

theorem UpperTheory.V.GC.decZhat :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∃ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) φ.1 ∧ ((Ine (F := F) A).subgroupOf (Dec (F := F) A) ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧
    ∀ n : ℕ, 0 < n → ∃ d : Dec (F := F) A →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ (Ine (F := F) A).subgroupOf (Dec (F := F) A), d s = 1) ∧ d φ = Multiplicative.ofAdd 1 := by
  intro F Ω _ _ _ _ _ v A hv
  exact dz_frob F Ω A v hv _ _ rfl rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GlobEuler
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

theorem UpperTheory.V.GC.globEuler :
    GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → IsTotallyReal F → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContAction ρ →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, IsCCAt w (c w)) → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
    finrank k (H1 ρ) + ∑ w, finrank k (LinearMap.ker (ρ (toGS Ω _ (c w)) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank ℚ F * finrank k M := by
  classical
  intro hF hE F Ω _ _ _ _ _ l _ hl hR S hS k _ _ _ M _ _ _ _ _ ρ hρ c hc
  haveI : Finite M := Module.finite_of_finite k
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  letI : Module (ZMod (l ^ 1)) M := Module.compHom _ (ZMod.castHom (dvd_refl _) k)
  let ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := map_add (ρ g)
          map_smul' := fun c m => map_smul (ρ g) (ZMod.castHom (dvd_refl _) k c) m }
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by
        rw [map_mul]; rfl }
  have e0 : H0 ρ ≃ H0 ρ' := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have e1 : H1 ρ ≃ H1 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ ≃ H2 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have ec : ∀ w, Nat.card {m : M // ρ' (toGS Ω _ (c w)) m = m} =
      Nat.card k ^ finrank k (LinearMap.ker (ρ (toGS Ω _ (c w)) - 1)) := fun w => by
    rw [← Module.natCard_eq_pow_finrank]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact Iff.rfl
  obtain ⟨-, f1, f2, -⟩ := hF F Ω l 1 M S ρ' one_pos hS hρ
  have h := hE F Ω l 1 M S ρ' one_pos hS hρ c fun w _ => hc w
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
    Finset.filter_true_of_mem fun w _ => hr w, Finset.prod_congr rfl fun w _ => ec w,
    Finset.prod_pow_eq_pow_sum] at h
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  haveI : Module.Finite k (H1 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k (H2 ρ) := Module.Finite.of_finite
  have hk : 1 < Nat.card k := Finite.one_lt_card
  refine ⟨inferInstance, inferInstance, ?_⟩
  apply Nat.pow_right_injective hk
  beta_reduce
  rw [pow_add, pow_add, pow_add, mul_comm (finrank ℚ F), pow_mul, ← Module.natCard_eq_pow_finrank (V := H1 ρ),
    ← Module.natCard_eq_pow_finrank (V := H0 ρ), ← Module.natCard_eq_pow_finrank (V := H2 ρ),
    ← Module.natCard_eq_pow_finrank (V := M),
    Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]
  exact h.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.H2RightExactModL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

section

variable {k G M : Type} [CommRing k] [Group G] [AddCommGroup M] [Module k M]

private theorem dn_two (ρ : Representation k G M) (b : (Fin 2 → G) → M) (x y z : G) :
    dn ρ 2 b ![x, y, z] = ρ x (b ![y, z]) - b ![x * y, z] + b ![x, y * z] - b ![x, y] := by
  have e0 : (fun i : Fin 2 => (![x, y, z] : Fin 3 → G) i.succ) = ![y, z] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (· * ·) (![x, y, z] : Fin 3 → G) = ![x * y, z] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.contractNth 1 (· * ·) (![x, y, z] : Fin 3 → G) = ![x, y * z] := by
    funext i; fin_cases i <;> rfl
  have e3 : Fin.contractNth 2 (· * ·) (![x, y, z] : Fin 3 → G) = ![x, y] := by
    funext i; fin_cases i <;> rfl
  change ρ _ (b _) + Finset.univ.sum (fun j : Fin 3 =>
      (-1 : k) ^ ((j : ℕ) + 1) • b (Fin.contractNth j (· * ·) ![x, y, z])) = _
  rw [Fin.sum_univ_three, e0, e1, e2, e3]
  have p3 : (-1 : k) ^ 3 = -1 := by ring
  simp [p3]
  abel

private theorem dn_three (ρ : Representation k G M) (b : (Fin 3 → G) → M) (x y z w : G) :
    dn ρ 3 b ![x, y, z, w] = ρ x (b ![y, z, w]) - b ![x * y, z, w] + b ![x, y * z, w]
      - b ![x, y, z * w] + b ![x, y, z] := by
  have e0 : (fun i : Fin 3 => (![x, y, z, w] : Fin 4 → G) i.succ) = ![y, z, w] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (· * ·) (![x, y, z, w] : Fin 4 → G) = ![x * y, z, w] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.contractNth 1 (· * ·) (![x, y, z, w] : Fin 4 → G) = ![x, y * z, w] := by
    funext i; fin_cases i <;> rfl
  have e3 : Fin.contractNth 2 (· * ·) (![x, y, z, w] : Fin 4 → G) = ![x, y, z * w] := by
    funext i; fin_cases i <;> rfl
  have e4 : Fin.contractNth 3 (· * ·) (![x, y, z, w] : Fin 4 → G) = ![x, y, z] := by
    funext i; fin_cases i <;> rfl
  change ρ _ (b _) + Finset.univ.sum (fun j : Fin 4 =>
      (-1 : k) ^ ((j : ℕ) + 1) • b (Fin.contractNth j (· * ·) ![x, y, z, w])) = _
  rw [Fin.sum_univ_four, e0, e1, e2, e3, e4]
  have p3 : (-1 : k) ^ 3 = -1 := by ring
  have p4 : (-1 : k) ^ 4 = 1 := by ring
  simp [p3, p4]
  abel

private theorem H2_map_surjective_of_H3_subsingleton [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace M] [DiscreteTopology M]
    {Q N : Type} [AddCommGroup Q] [Module k Q] [TopologicalSpace Q] [DiscreteTopology Q]
    [AddCommGroup N] [Module k N] [TopologicalSpace N] [DiscreteTopology N]
    (ρ : Representation k G M) (σ : Representation k G Q) (τ : Representation k G N) (hc : ContAction ρ)
    (q : M →ₗ[k] Q) (hq : ∀ s m, q (ρ s m) = σ s (q m)) (hs : Function.Surjective q)
    (i : N →ₗ[k] M) (hi : ∀ s m, i (τ s m) = ρ s (i m)) (hinj : Function.Injective i)
    (hex : ∀ m, q m = 0 ↔ ∃ n, i n = m) (h3 : Subsingleton (Hn τ 3)) :
    Function.Surjective (mapH2 ρ σ q continuous_of_discreteTopology hq) := by
  classical
  intro cl
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ cl
  obtain ⟨sec, hsec⟩ := hs.hasRightInverse
  let Φ : G × G → M := fun p => sec (f.1 p)
  have hΦ : Continuous Φ := continuous_of_discreteTopology.comp f.2.1
  have hqΦ : ∀ p, q (Φ p) = f.1 p := fun p => hsec _
  let c : (Fin 3 → G) → M := fun g =>
    ρ (g 0) (Φ (g 1, g 2)) - Φ (g 0 * g 1, g 2) + Φ (g 0, g 1 * g 2) - Φ (g 0, g 1)
  have hcc : Continuous c := by
    have h0 : Continuous fun g : Fin 3 → G => ρ (g 0) (Φ (g 1, g 2)) :=
      hc.comp (f := fun g : Fin 3 → G => (g 0, Φ (g 1, g 2))) (by fun_prop)
    exact ((h0.sub (by fun_prop)).add (by fun_prop)).sub (by fun_prop)
  have hqc : ∀ g, q (c g) = 0 := fun g => by
    simp only [c, map_sub, map_add (f := _), hq, hqΦ]
    exact f.2.2 _ _ _
  let r : M → N := Function.invFun i
  have hr : ∀ g, i (r (c g)) = c g := fun g => Function.invFun_eq ((hex _).1 (hqc g))
  obtain ⟨b, hb, hbc⟩ := (GlobalTheory.Published.subsingleton_Hn_succ_iff τ 2).1 h3 (fun g => r (c g))
    ((continuous_of_discreteTopology (f := r)).comp hcc) (by
      funext g
      obtain ⟨x, y, z, w, rfl⟩ : ∃ x y z w, g = ![x, y, z, w] :=
        ⟨g 0, g 1, g 2, g 3, by funext j; fin_cases j <;> rfl⟩
      apply hinj
      rw [dn_three]
      simp only [map_add (f := _), map_sub, hi, hr, Pi.zero_apply, map_zero]
      simp [c, mul_assoc]
      abel)
  have hb' : Continuous fun p : G × G => i (b ![p.1, p.2]) :=
    continuous_of_discreteTopology.comp (hb.comp (by fun_prop))
  refine ⟨Submodule.Quotient.mk ⟨fun p => Φ p - i (b ![p.1, p.2]), hΦ.sub hb', fun x y z => ?_⟩, ?_⟩
  · have e := congrArg i (congrFun hbc ![x, y, z])
    rw [dn_two] at e
    simp only [map_add (f := _), map_sub, hi, hr] at e
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at e
    simp only [map_sub]
    rw [← sub_eq_zero.2 e.symm]
    abel
  · change Submodule.Quotient.mk _ = _
    congr 1
    apply Subtype.ext
    funext p
    change q (Φ p - i (b ![p.1, p.2])) = _
    rw [map_sub, hqΦ, (hex _).2 ⟨_, rfl⟩, sub_zero]

end

theorem UpperTheory.V.GC.local_second_cohomology_surjective_at_place :
    LocalFiniteness → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (Q : Type) [AddCommGroup Q] [Module k Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (ρ : Representation k (Dec (F := F) A) M) (σ : Representation k (Dec (F := F) A) Q), ContAction ρ → ∀ (q : M →ₗ[k] Q) (hq : ∀ s m, q (ρ s m) = σ s (q m)), Function.Surjective q →
    Function.Surjective (mapH2 ρ σ q continuous_of_discreteTopology hq) := by
  intro hLF F Ω _ _ _ _ _ l _ v A hA k _ _ _ M _ _ _ _ _ Q _ _ _ _ ρ σ hc q hq hs
  haveI : Finite M := Module.finite_of_finite k
  have hst : ∀ g, LinearMap.ker q ≤ (LinearMap.ker q).comap (ρ g) := fun g m hm => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, hq, LinearMap.mem_ker.1 hm, map_zero]
  let τ := ρ.subrepresentation (LinearMap.ker q) hst
  have hτ : ContAction τ :=
    Continuous.subtype_mk (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
  refine H2_map_surjective_of_H3_subsingleton ρ σ τ hc q hq hs (LinearMap.ker q).subtype (fun _ _ => rfl) Subtype.val_injective
    (fun m => ⟨fun h => ⟨⟨m, h⟩, rfl⟩, by rintro ⟨n, rfl⟩; exact n.2⟩) ?_
  refine (GlobalTheory.Published.cohDimTwoLocal_of_localFiniteness hLF).of_nsmul l 1 (fun m => ?_) τ hA hτ 3 le_rfl
  rw [pow_one, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.IsClosedOfClosedFiniteIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem isClosed_of_closed_finite_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (I J : Subgroup Γ) (hJI : J ≤ I) (hJ : IsClosed (J : Set Γ)) (h : J.relIndex I ≠ 0) : IsClosed (I : Set Γ) := by
  haveI : (J.subgroupOf I).FiniteIndex := ⟨h⟩
  have e : (I : Set Γ) = ⋃ q : I ⧸ J.subgroupOf I, (fun g : Γ => ((q.out : I) : Γ)⁻¹ * g) ⁻¹' (J : Set Γ) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hg
      refine ⟨(QuotientGroup.mk (⟨g, hg⟩ : I)), ?_⟩
      have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨g, hg⟩ : I) : I ⧸ J.subgroupOf I))
      exact Subgroup.mem_subgroupOf.1 this
    · rintro ⟨q, hq⟩
      have := I.mul_mem (q.out : I).2 (hJI hq)
      rwa [mul_inv_cancel_left] at this
  rw [e]
  exact isClosed_iUnion_of_finite fun q => hJ.preimage (by fun_prop)

theorem UpperTheory.V.GC.H2_unramified_inflation :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M), ContAction ρ → ∀ (I J : Subgroup Γ) [I.Normal] [J.Normal] (φ : Γ), J ≤ I → IsClosed (J : Set Γ) → ¬ l ∣ J.relIndex I → (∀ j ∈ J, ρ j = 1) →
    (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ → (∀ n : ℕ, 0 < n → ∃ d : Γ →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
    ∀ z : Z2 ρ, (∀ s t, ∀ j ∈ J, ∀ j' ∈ J, z.1 (s * j, t * j') = z.1 (s, t)) → ∃ b : Γ → M, IsLocallyConstant b ∧ (∀ s, ∀ j ∈ J, b (s * j) = b s) ∧ ∀ s t, z.1 (s, t) = ρ s (b t) - b (s * t) + b s := by
  intro l hl Γ _ _ _ _ _ _ k _ _ _ M _ _ _ _ _ ρ hρ I J _ _ φ hJI hJ hidx hJρ hφ hd z hz
  haveI : Finite M := Module.finite_of_finite k
  have hker : IsOpen (ρ.ker : Set Γ) := by
    have e : (ρ.ker : Set Γ) = ⋂ m : M, (fun g : Γ => ρ g m) ⁻¹' {m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [e]
    exact isOpen_iInter_of_finite fun m =>
      (isOpen_discrete _).preimage (Continuous.comp hρ (Continuous.prodMk_left m))
  have hI : IsClosed (I : Set Γ) := isClosed_of_closed_finite_index I J hJI hJ (fun h => hidx (h ▸ dvd_zero l))
  obtain ⟨a, ha1, ha2, ha3⟩ := UpperTheory.V.Alg.exists_locallyConstant_dOne_eq_cocycle_of_tame_inertia l k Γ M ρ hker I J hI hJ hJI (fun j hj => hJρ j hj) hidx ⟨φ, hφ⟩
    (by
      intro n
      obtain ⟨d, hd1, hd2, hd3⟩ := hd (l ^ n) (pow_pos hl.out.pos n)
      haveI : NeZero (l ^ n) := ⟨(pow_pos hl.out.pos n).ne'⟩
      refine ⟨d.ker, hd1.isOpen_fiber 1, fun s hs => hd2 s hs, ?_⟩
      have hs : d.range = ⊤ := by
        rw [eq_top_iff]
        intro x _
        refine ⟨φ ^ (Multiplicative.toAdd x).val, ?_⟩
        rw [map_pow, hd3, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
      rw [Subgroup.index_ker, hs, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod])
    z.1 ((IsLocallyConstant.iff_continuous _).2 z.2.1)
    (by
      intro s t u
      have e := z.2.2 s t u
      rw [← sub_eq_zero, ← e]
      abel) hz
  refine ⟨a, ha1, ha2, fun s t => ?_⟩
  rw [← ha3]
  simp only [UpperTheory.V.Alg.dOne]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LevelS
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem ine_le_open (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Subgroup (G F Ω)) (hK : IsOpen (K : Set (G F Ω))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      Ine (F := F) A ≤ K := by
  obtain ⟨E, hE, hEK⟩ := (krullTopology_mem_nhds_one_iff F Ω (K : Set (G F Ω))).1 (hK.mem_nhds K.one_mem)
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure E Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  obtain ⟨T, hT⟩ := (Base.ramFinite F F E Ω).1
  refine ⟨T, fun v hv A hA g hg => hEK ?_⟩
  have h := hT v hv A hA (show g ∈ Base.galOf F F Ω ⊓ Ine (F := F) A from ⟨fun x => g.commutes x, hg⟩)
  exact (IntermediateField.mem_fixingSubgroup_iff E g).2 fun x hx => h ⟨x, hx⟩

theorem UpperTheory.V.GC.levelS :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ), GLink l S K π →
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 F))) (p : GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))) →* Γ), S ⊆ S' ∧ Continuous p ∧ Function.Surjective p ∧ p.comp (toGS Ω _) = π ∧ ∀ A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (A v) v) →
    p.ker = (Subgroup.normalClosure (⋃ q : {v // v ∈ S' ∧ v ∉ S}, (((Ine (F := F) (A q.1) ⊓ K).map (toGS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))) : Subgroup _) : Set (GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))))))).topologicalClosure := by
  intro F Ω _ _ _ _ _ l _ S K Γ _ _ _ _ _ _ π h
  classical
  obtain ⟨T, hT⟩ := ine_le_open F Ω K h.isOpen
  have hgen : ∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ g ∈ Ine (F := F) B, g ∈ K → π g = 1 := by
    intro v hv B hB g hg hgK
    rw [← MonoidHom.mem_ker, h.ker]
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
    simp only [Set.mem_iUnion]
    exact ⟨v, hv, B, hB, hg, hgK⟩
  have hcl : IsClosed (π.ker : Set (G F Ω)) := isClosed_singleton.preimage h.cont
  have hNS : NS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))) ≤ π.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, B, hB, hg⟩ := hg
    exact hgen v (fun h' => hv (Finset.mem_union_left _ h')) B hB g hg
      (hT v (fun h' => hv (Finset.mem_union_right _ h')) B hB hg)
  have hp : Continuous (QuotientGroup.lift _ π hNS) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 h.cont
  refine ⟨S ∪ T, QuotientGroup.lift _ π hNS, Finset.subset_union_left, hp, fun y => ?_, rfl, fun A hA => ?_⟩
  · obtain ⟨g, rfl⟩ := h.onto y
    exact ⟨toGS Ω _ g, rfl⟩
  generalize hN : (Subgroup.normalClosure (⋃ q : {v // v ∈ S ∪ T ∧ v ∉ S}, (((Ine (F := F) (A q.1) ⊓ K).map
    (toGS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F)))) : Subgroup _) :
      Set (GS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))))))).topologicalClosure = N
  haveI hNn : N.Normal := by
    rw [← hN]
    exact Subgroup.is_normal_topologicalClosure _
  have hNc : IsClosed (N : Set (GS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))))) := by
    rw [← hN]
    exact Subgroup.isClosed_topologicalClosure _
  apply le_antisymm
  · have key : π.ker ≤ N.comap (toGS Ω _) := by
      rw [h.ker]
      refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
        (hNc.preimage QuotientGroup.continuous_mk)
      intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨v, hv, B, hB, hg, hgK⟩ := hg
      by_cases hvS : v ∈ S ∪ T
      · obtain ⟨u, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA v) hB
        have hm : u⁻¹ * g * u ∈ N.comap (toGS Ω _) := by
          rw [← hN]
          refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
          exact Set.mem_iUnion.2 ⟨⟨v, hvS, hv⟩,
            Subgroup.mem_map_of_mem _ ⟨GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg, h.normal.conj_mem' g hgK u⟩⟩
        have := (hNn.comap (toGS Ω _)).conj_mem _ hm u
        simpa [mul_assoc] using this
      · have h1 : toGS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))) g = 1 := by
          refine (QuotientGroup.eq_one_iff g).2 ?_
          refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
          simp only [Set.mem_iUnion]
          exact ⟨v, hvS, B, hB, hg⟩
        show toGS Ω _ g ∈ N
        rw [h1]
        exact N.one_mem
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact key hx
  · rw [← hN]
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) (isClosed_singleton.preimage hp)
    intro x hx
    obtain ⟨q, g, hg, rfl⟩ := Set.mem_iUnion.1 hx
    exact hgen q.1 q.2.2 _ (hA q.1) g hg.1 hg.2
end

