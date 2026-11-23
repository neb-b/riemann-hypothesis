module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.ActU
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.h90 :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (l : ℕ), IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → ∀ x y : Fˣ, actU γ x = x * y ^ l → Algebra.norm L (y : F) = 1 → ∃ (x₀ : Lˣ) (z : Fˣ), x = Units.map (algebraMap L F : L →* F) x₀ * z ^ l := by
  intro L F _ _ _ _ _ γ l hG hγ x y hx hy
  haveI : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite ℚ L F
  haveI : IsCyclic (F ≃ₐ[L] F) := ⟨⟨γ, hγ⟩⟩
  obtain ⟨w, hw⟩ := groupCohomology.exists_div_of_norm_eq_one hγ hy
  have hx' : γ (x : F) = (x : F) * (y : F) ^ l := by
    have := congrArg (fun u : Fˣ => (u : F)) hx
    simpa [actU] using this
  have hw0 : (w : F) ≠ 0 := w.ne_zero
  have hgw0 : γ (w : F) ≠ 0 := by simp
  have hfix : γ ((x : F) * (w : F) ^ l) = (x : F) * (w : F) ^ l := by
    rw [map_mul, map_pow, hx', ← hw, mul_assoc, ← mul_pow, div_mul_cancel₀ _ hgw0]
  have hall : ∀ σ : F ≃ₐ[L] F, σ ((x : F) * (w : F) ^ l) = (x : F) * (w : F) ^ l := by
    intro σ
    have hle : Subgroup.zpowers γ ≤ MulAction.stabilizer (F ≃ₐ[L] F) ((x : F) * (w : F) ^ l) := by
      rw [Subgroup.zpowers_le]
      exact hfix
    exact hle (hγ σ)
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hall
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (mul_ne_zero x.ne_zero (pow_ne_zero l hw0)) ha.symm
  refine ⟨Units.mk0 a ha0, w⁻¹, ?_⟩
  ext
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0, ha,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hw0, one_pow, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.ActUPow
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem dat_g_pow_apply_ofMul_eq_actU_inv_pow {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (hD : IsDat γ a D)
    (k : ℕ) (α : Fˣ) :
    (D.g ^ k) (Additive.ofMul α) = Additive.ofMul (actU (γ⁻¹ ^ k) α) := by
  induction k generalizing α with
  | zero => simp [actU]; rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, hD.g_eq, ih]
    congr 1

private theorem dat_nm_apply_ofMul_eq_ofMul_nrm {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (hD : IsDat γ a D)
    (α : Fˣ) :
    D.nm (Additive.ofMul α) = Additive.ofMul (nrm γ a α) := by
  simp only [Dat.nm, LinearMap.sum_apply, LinearMap.smul_apply, nrm, ofMul_prod, ofMul_pow, hD.n_eq,
    hD.a_eq, dat_g_pow_apply_ofMul_eq_actU_inv_pow γ a D hD]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ orderOf γ := (Finset.mem_range.mp hj).le
  have hinv : (γ⁻¹) ^ (orderOf γ - j) = γ ^ j := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, Nat.sub_add_cancel hj', pow_orderOf_eq_one]
  rw [hinv]
  push_cast
  exact natCast_zsmul _ _

theorem UpperTheory.V.ZK.Ct.fewLe :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a s q B : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsDat γ a D → Few γ a s q B → ∀ f : D.W →ₗ[ℤ] Additive Fˣ ⧸ mt (Additive Fˣ) q, (∀ y : D.U, f (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((s : ℤ) • D.nm y)) → Finite D.W → Nat.card (LinearMap.range f) ≤ B := by
  intro L F _ _ _ _ _ γ a s q B D hD hF f hf hW
  classical
  haveI : Finite (LinearMap.range f) := Finite.of_surjective _ f.surjective_rangeRestrict
  haveI := Fintype.ofFinite (LinearMap.range f)
  choose w hw using fun z : LinearMap.range f => LinearMap.mem_range.mp z.2
  choose u hu using fun z : LinearMap.range f => Submodule.Quotient.mk_surjective _ (w z)
  have hφ : ∀ z, f (Submodule.Quotient.mk (u z)) = z := by
    intro z
    rw [hu, hw]
  let φ : LinearMap.range f → Fˣ := fun z => Additive.toMul ((u z : D.U) : Additive Fˣ)
  have hinj : Function.Injective φ := by
    intro z z' h
    have h' : u z = u z' := Subtype.ext (Additive.toMul.injective h)
    apply Subtype.ext
    rw [← hφ z, ← hφ z', h']
  have key := hF (Finset.univ.image φ) ?_ ?_
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card] at key
    exact key
  · intro α hα
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨𝔡, h𝔡⟩ := LinearMap.mem_range.mp (u z).2
    refine ⟨𝔡, fun P => ?_⟩
    have hP := congrArg (fun x => x P) h𝔡
    have hd : ordP P (φ z) = D.d ((u z : D.U) : Additive Fˣ) P := (hD.d_eq _ P).symm
    rw [hd, ← hP]
    simp [Dat.delI, hD.gI_eq, hD.a_eq]
  · intro α hα α' hα' ⟨δ, hδ⟩
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨z', -, rfl⟩ := Finset.mem_image.mp hα'
    congr 1
    apply Subtype.ext
    rw [← hφ z, ← hφ z', hf, hf, Submodule.Quotient.eq]
    apply Submodule.mem_sup_left
    refine LinearMap.mem_range.mpr ⟨Additive.ofMul δ, ?_⟩
    have e := congrArg Additive.ofMul hδ
    rw [ofMul_mul, ofMul_pow, ofMul_pow, ofMul_pow] at e
    have e1 := dat_nm_apply_ofMul_eq_ofMul_nrm γ a D hD (φ z)
    have e2 := dat_nm_apply_ofMul_eq_ofMul_nrm γ a D hD (φ z')
    change D.nm (u z : Additive Fˣ) = _ at e1
    change D.nm (u z' : Additive Fˣ) = _ at e2
    rw [e1, e2, natCast_zsmul, natCast_zsmul, e]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardKerEqCoker
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

section SlopeTestRemainingChoices

variable {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I)

private theorem delI_inj : Function.Injective D.delI := by
  refine (injective_iff_map_eq_zero D.delI).2 fun z hz => ?_
  have hg : D.gI z = D.a • z := by
    simp [Dat.delI, sub_eq_zero] at hz
    exact hz
  have hk : ∀ k : ℕ, (D.gI ^ k) z = (D.a ^ k) • z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_nsmul, hg, smul_smul, ← pow_succ]
  have h1 := hk D.n
  rw [D.gI_pow, Module.End.one_apply] at h1
  have ha : (2 : ℤ) ≤ D.a := by exact_mod_cast D.two_le
  have hp : (2 : ℤ) ^ 1 ≤ (D.a : ℤ) ^ D.n :=
    le_trans (pow_le_pow_right₀ (by norm_num) D.n_pos) (pow_le_pow_left₀ (by norm_num) ha _)
  have hne : (D.a : ℤ) ^ D.n - 1 ≠ 0 := by
    norm_num at hp
    omega
  have hc : ((D.a : ℤ) ^ D.n) • z = (D.a ^ D.n) • z := by
    rw [← Nat.cast_pow, natCast_zsmul]
  refine D.tf _ z hne ?_
  rw [sub_smul, one_smul, hc, ← h1, sub_self]

private theorem d_del (y : Y) : D.d (D.del y) = D.delI (D.d y) := by
  simp [Dat.del, Dat.delI, D.comm]

private theorem d_tors {t : Y} (ht : t ∈ Submodule.torsion ℤ Y) : D.d t = 0 := by
  obtain ⟨m, hm⟩ := (Submodule.mem_torsion_iff t).1 ht
  have hm' : (m : ℤ) • t = 0 := hm
  refine D.tf m _ (nonZeroDivisors.coe_ne_zero m) ?_
  rw [← map_zsmul, hm', map_zero]

private theorem card_ker_eq_coker {C : Type} [AddCommGroup C] [Finite C] (f : C →ₗ[ℤ] C) :
    Nat.card (LinearMap.ker f) = Nat.card (C ⧸ LinearMap.range f) := by
  have h1 : Nat.card C = Nat.card (C ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup
  have h2 : Nat.card C = Nat.card (C ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range f).toAddSubgroup
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (h2.trans (mul_comm _ _)))

private theorem exists_psi : ∃ ψ : D.U →ₗ[ℤ] I, ∀ u : D.U, D.delI (ψ u) = D.d u := by
  let e := LinearEquiv.ofInjective D.delI (delI_inj D)
  let c : D.U →ₗ[ℤ] LinearMap.range D.delI :=
    (D.d ∘ₗ D.U.subtype).codRestrict (LinearMap.range D.delI) (fun u => u.2)
  refine ⟨e.symm.toLinearMap ∘ₗ c, fun u => ?_⟩
  have h := LinearEquiv.ofInjective_apply D.delI (h := delI_inj D) (e.symm (c u))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end SlopeTestRemainingChoices

theorem UpperTheory.V.ZK.Ct.cardW :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), Finite (I ⧸ LinearMap.range D.d) → Finite D.EQ → Finite D.ClQ ∧ Finite D.W ∧ Nat.card D.W = Nat.card D.EQ * Nat.card D.ClQ := by
  intro Y I _ _ D hC hE
  obtain ⟨ψ, hψ⟩ := exists_psi D
  have hψ0 : ∀ u : D.U, D.d u = 0 → ψ u = 0 := fun u hu =>
    delI_inj D (by rw [hψ, hu, map_zero])
  let S := (LinearMap.range D.del ⊔ Submodule.torsion ℤ Y).submoduleOf D.U
  let p := LinearMap.range D.d
  have hpf : p ≤ p.comap D.delI := by
    rintro _ ⟨y, rfl⟩
    exact ⟨D.del y, d_del D y⟩
  let f : (I ⧸ p) →ₗ[ℤ] (I ⧸ p) := p.mapQ p D.delI hpf
  let φ : D.U →ₗ[ℤ] I ⧸ p := p.mkQ ∘ₗ ψ
  have hSφ : S ≤ LinearMap.ker φ := by
    intro u hu
    change (u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y at hu
    obtain ⟨a, ⟨y, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 hu
    have hy : ψ u = D.d y :=
      delI_inj D (by rw [hψ, ← hat, map_add (f := _), d_tors D ht, add_zero, d_del])
    change p.mkQ (ψ u) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hy]
    exact LinearMap.mem_range_self _ _
  let φb : D.W →ₗ[ℤ] I ⧸ p := S.liftQ φ hSφ
  have hkU : LinearMap.ker D.d ≤ D.U := fun y hy => by
    change D.d y ∈ LinearMap.range D.delI
    rw [LinearMap.mem_ker.1 hy]
    exact zero_mem _
  let ι : LinearMap.ker D.d →ₗ[ℤ] D.W := S.mkQ ∘ₗ Submodule.inclusion hkU
  have hrange : LinearMap.range φb = LinearMap.ker f := by
    show LinearMap.range (S.liftQ φ hSφ) = LinearMap.ker f
    rw [Submodule.range_liftQ]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      change (Submodule.Quotient.mk (D.delI (ψ u)) : I ⧸ p) = 0
      rw [hψ, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self _ _
    · intro hx
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p x
      rw [LinearMap.mem_ker] at hx
      change (Submodule.Quotient.mk (D.delI x) : I ⧸ p) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy⟩ := hx
      have hyU : y ∈ D.U := ⟨x, hy.symm⟩
      have hψy : ψ ⟨y, hyU⟩ = x := delI_inj D (by rw [hψ]; exact hy)
      refine ⟨⟨y, hyU⟩, ?_⟩
      show p.mkQ (ψ ⟨y, hyU⟩) = p.mkQ x
      rw [hψy]
  have hker : LinearMap.ker φb = LinearMap.range ι := by
    ext w
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective S w
    constructor
    · intro hu
      rw [LinearMap.mem_ker] at hu
      change p.mkQ (ψ u) = 0 at hu
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu
      obtain ⟨y, hy⟩ := hu
      have hk : (u : Y) - D.del y ∈ LinearMap.ker D.d := by
        rw [LinearMap.mem_ker, map_sub, d_del, hy, ← hψ, sub_self]
      refine ⟨⟨_, hk⟩, ?_⟩
      change S.mkQ (Submodule.inclusion hkU ⟨_, hk⟩) = S.mkQ u
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      change ((u : Y) - D.del y - u) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y
      rw [sub_sub_cancel_left]
      exact Submodule.mem_sup_left (Submodule.neg_mem _ (LinearMap.mem_range_self _ _))
    · rintro ⟨k, hk⟩
      rw [LinearMap.mem_ker, ← hk]
      have hk0 : ψ (Submodule.inclusion hkU k) = 0 := hψ0 _ k.2
      change p.mkQ (ψ (Submodule.inclusion hkU k)) = 0
      rw [hk0, map_zero]
  have hkerι : LinearMap.ker ι = (Submodule.map D.del (LinearMap.ker D.d) ⊔
      Submodule.torsion ℤ Y).submoduleOf (LinearMap.ker D.d) := by
    ext k
    rw [LinearMap.mem_ker]
    change S.mkQ (Submodule.inclusion hkU k) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (k : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y ↔
      (k : Y) ∈ Submodule.map D.del (LinearMap.ker D.d) ⊔ Submodule.torsion ℤ Y
    constructor
    · intro h
      obtain ⟨a, ⟨y, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 h
      have hy : D.d y = 0 := by
        apply delI_inj D
        rw [map_zero, ← d_del]
        have hk := k.2
        rw [LinearMap.mem_ker, ← hat, map_add (f := _), d_tors D ht, add_zero] at hk
        exact hk
      exact Submodule.mem_sup.2 ⟨D.del y, ⟨y, hy, rfl⟩, t, ht, hat⟩
    · intro h
      obtain ⟨a, ⟨y, -, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 h
      exact Submodule.mem_sup.2 ⟨D.del y, LinearMap.mem_range_self _ _, t, ht, hat⟩
  haveI : Finite (I ⧸ p) := hC
  haveI : Finite D.EQ := hE
  have hr : LinearMap.range f = Submodule.map p.mkQ (LinearMap.range D.delI) :=
    calc LinearMap.range f = LinearMap.range (f ∘ₗ p.mkQ) :=
          (LinearMap.range_comp_of_range_eq_top f (Submodule.range_mkQ p)).symm
      _ = LinearMap.range (p.mkQ ∘ₗ D.delI) := by rw [Submodule.mapQ_mkQ]
      _ = Submodule.map p.mkQ (LinearMap.range D.delI) := LinearMap.range_comp _ _
  have hQ : Finite ((I ⧸ p) ⧸ Submodule.map p.mkQ (LinearMap.range D.delI)) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hClQ : Finite D.ClQ :=
    Finite.of_equiv _ (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv
  have hcoker : Nat.card D.ClQ = Nat.card ((I ⧸ p) ⧸ LinearMap.range f) := by
    rw [hr]
    exact Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv.symm
  have hkf := card_ker_eq_coker f
  have hEQ : Nat.card D.EQ = Nat.card (LinearMap.range ι) :=
    Nat.card_congr ((Submodule.quotEquivOfEq _ _ hkerι.symm).trans ι.quotKerEquivRange).toEquiv
  have hW : Nat.card D.W = Nat.card (D.W ⧸ LinearMap.ker φb) * Nat.card (LinearMap.ker φb) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker φb).toAddSubgroup
  have hmain : Nat.card D.W = Nat.card D.EQ * Nat.card D.ClQ := by
    rw [hW, Nat.card_congr φb.quotKerEquivRange.toEquiv, hrange, hkf, ← hcoker, hker, ← hEQ]
    exact mul_comm _ _
  have hne : Nat.card D.W ≠ 0 := by
    rw [hmain]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  exact ⟨hClQ, Nat.finite_of_card_ne_zero hne, hmain⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CountOrdP
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct
open scoped nonZeroDivisors

private theorem fractionalIdeal_count_spanSingleton_eq_ordP {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    FractionalIdeal.count F P (FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F)) = ordP P x := by
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (𝓞 F) (x : F)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hrs
    exact x.ne_zero hrs.symm
  have hI : FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F) s)⁻¹ * ↑(Ideal.span {r}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← hrs, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined F P (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact x.ne_zero) hI]
  unfold ordP
  rw [← hrs, map_div₀]
  erw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  rw [HeightOneSpectrum.intValuation_if_neg _ hr0, HeightOneSpectrum.intValuation_if_neg _ hs0,
    ← WithZero.exp_sub, WithZero.log_exp]
  ring

theorem UpperTheory.V.ZK.Ct.clFin :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsDat γ a D → Finite ((HeightOneSpectrum (𝓞 F) →₀ ℤ) ⧸ LinearMap.range D.d) := by
  intro L F _ _ _ _ _ γ a D hD
  classical
  obtain ⟨I, hI⟩ : ∃ I : (HeightOneSpectrum (𝓞 F) →₀ ℤ) → (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      ∀ e P, FractionalIdeal.count F P (I e : FractionalIdeal (𝓞 F)⁰ F) = e P :=
    ⟨fun e => Units.mk0 (e.prod fun P n => ((P.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ^ n)
      (Finset.prod_ne_zero_iff.mpr fun P _ =>
        zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot)),
      fun e P => FractionalIdeal.count_finsuppProd F P e⟩
  have key : ∀ e e', ClassGroup.mk F (I e) = ClassGroup.mk F (I e') → e - e' ∈ LinearMap.range D.d := by
    intro e e' h
    have h' : ClassGroup.mk F (I e * (I e')⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.1 h').principal
    have hJ : ((I e * (I e')⁻¹ : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
      apply FractionalIdeal.coeToSubmodule_injective
      dsimp only
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [FractionalIdeal.spanSingleton_zero] at hJ
      exact Units.ne_zero _ hJ
    refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
    ext P
    rw [hD.d_eq, Finsupp.coe_sub, Pi.sub_apply, ← hI e P, ← hI e' P, ← fractionalIdeal_count_spanSingleton_eq_ordP, Units.val_mk0, ← hJ,
      Units.val_mul, Units.val_inv_eq_inv_val,
      FractionalIdeal.count_mul F P (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _)),
      FractionalIdeal.count_inv]
    ring
  refine Finite.of_injective (fun q => ClassGroup.mk F (I (Quotient.out q))) ?_
  intro q1 q2 h
  rw [← Submodule.Quotient.mk_out q1, ← Submodule.Quotient.mk_out q2]
  exact (Submodule.Quotient.eq _).2 (key _ _ h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.LatDet
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.latDet :
    ∀ (E V : Type) [AddCommGroup E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (lam : E →ₗ[ℤ] V) (δ : Module.End ℤ E) (δV : V →ₗ[ℝ] V), (∀ x, lam (δ x) = δV (lam x)) → LinearMap.ker lam = Submodule.torsion ℤ E → DiscreteTopology (LinearMap.range lam) → Submodule.span ℝ (LinearMap.range lam : Set V) = ⊤ → LinearMap.det δV ≠ 0 → Finite (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) ∧ (Nat.card (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) : ℝ) = |LinearMap.det δV| := by
  intro E V _ _ _ _ lam δ δV hcomm hker hdisc hspan hdet
  classical
  set L := LinearMap.range lam with hL
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  have hmaps : ∀ x ∈ L, (δV.restrictScalars ℤ) x ∈ L := by
    rintro _ ⟨y, rfl⟩
    exact ⟨δ y, by simp [hcomm]⟩
  set f : L →ₗ[ℤ] L := (δV.restrictScalars ℤ).restrict hmaps with hf
  have hfv : ∀ y : L, ((f y : L) : V) = δV y := fun y => rfl
  have hVinj : Function.Injective δV := fun a b h =>
    (LinearMap.equivOfDetNeZero δV hdet).injective h
  have hfinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply hVinj
    rw [← hfv, ← hfv, h]
  have hcard : Nat.card (L ⧸ LinearMap.range f) = (LinearMap.det f).natAbs := by
    rw [← Submodule.natAbs_det_equiv (LinearMap.range f) (LinearEquiv.ofInjective f hfinj)]
    congr 2
  have hdetf : ((LinearMap.det f : ℤ) : ℝ) = LinearMap.det δV := by
    let b := Module.Free.chooseBasis ℤ L
    let bV := b.ofZLatticeBasis ℝ L
    have hM : (Int.castRingHom ℝ).mapMatrix (LinearMap.toMatrix b b f) =
        LinearMap.toMatrix bV bV δV := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, eq_intCast]
      rw [show bV j = ((b j : L) : V) from b.ofZLatticeBasis_apply ℝ L j, ← hfv,
        Module.Basis.ofZLatticeBasis_repr_apply]
    rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bV, ← hM, ← RingHom.map_det,
      eq_intCast]
  have hne : (LinearMap.det f).natAbs ≠ 0 := by
    intro h
    apply hdet
    rw [← hdetf, Int.natAbs_eq_zero.mp h, Int.cast_zero]
  let g : E →ₗ[ℤ] L ⧸ LinearMap.range f := (LinearMap.range f).mkQ ∘ₗ lam.rangeRestrict
  have hgs : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp lam.surjective_rangeRestrict
  have hkerg : LinearMap.ker g = LinearMap.range δ ⊔ Submodule.torsion ℤ E := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_sup, LinearMap.mem_range]
    constructor
    · rintro ⟨⟨_, z, rfl⟩, hz⟩
      refine ⟨δ z, ⟨z, rfl⟩, x - δ z, ?_, by abel⟩
      rw [← hker, LinearMap.mem_ker, map_sub, sub_eq_zero]
      have := congrArg Subtype.val hz
      rw [hfv] at this
      simpa [hcomm] using this.symm
    · rintro ⟨_, ⟨z, rfl⟩, t, ht, rfl⟩
      rw [← hker, LinearMap.mem_ker] at ht
      refine ⟨lam.rangeRestrict z, Subtype.ext ?_⟩
      rw [hfv]
      simp [hcomm, ht]
  let e2 : (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) ≃ₗ[ℤ] L ⧸ LinearMap.range f :=
    (Submodule.quotEquivOfEq _ _ hkerg.symm).trans (g.quotKerEquivOfSurjective hgs)
  haveI : Finite (L ⧸ LinearMap.range f) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  refine ⟨Finite.of_equiv _ e2.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e2.toEquiv, hcard, Nat.cast_natAbs, Int.cast_abs, hdetf]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.Places
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.places :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F), IsTotallyComplex L → IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → IsTotallyComplex F ∧ Fintype.card (InfinitePlace F) = orderOf γ * InfinitePlace.nrComplexPlaces L ∧ ∀ (k : ℕ) (w : InfinitePlace F), γ ^ k • w = w ↔ orderOf γ ∣ k := by
  intro L F _ _ _ _ _ γ hL hG hγ
  haveI := hL
  haveI : IsTotallyComplex F := isTotallyComplex_of_algebra L F
  haveI : IsUnramifiedAtInfinitePlaces L F :=
    ⟨fun w => InfinitePlace.isUnramified_iff.mpr (Or.inr (IsTotallyComplex.isComplex _))⟩
  have htop : Subgroup.zpowers γ = ⊤ := eq_top_iff.mpr fun σ _ => hγ σ
  have hcard : Module.finrank L F = orderOf γ := by
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_zpowers, htop, Subgroup.card_top]
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [IsUnramifiedAtInfinitePlaces.card_infinitePlace L F, hcard,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, mul_comm]
  · intro k w
    have hst := (InfinitePlace.isUnramified L w).stabilizer_eq_bot
    rw [orderOf_dvd_iff_pow_eq_one, ← MulAction.mem_stabilizer_iff, hst, Subgroup.mem_bot]
end

