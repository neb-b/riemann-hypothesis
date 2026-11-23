module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.BaseExt
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

section Prescribed

def toComap {F K : IntermediateField ℚ ℂ} (h : F ≤ K) : F →+* (F.comap K.val) where
  toFun x := ⟨⟨x, h x.2⟩, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem image_comap {E : Type} [Field E] {F K : IntermediateField ℚ ℂ} (h : F ≤ K) (𝔞 : Ideal (𝓞 E)) (τ : E →+* ℂ)
    (e : E → K) (he : ∀ a, (e a : ℂ) = τ a) :
    extend (toComap h) (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)}) =
      Submodule.span (𝓞 (F.comap K.val)) {x : F.comap K.val | ∃ a ∈ 𝔞, (x : K) = e (a : E)} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, Subtype.ext (hy.trans (he _).symm)⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨⟨x.1.1, x.2⟩, ⟨a, ha, (congrArg Subtype.val hx).trans (he _)⟩, rfl⟩

theorem exists_gens_le (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] : ∃ S : Finset ℂ,
    (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ K) → F ≤ K := by
  have : NumberField F := NumberField.mk
  obtain ⟨S, hS, h⟩ := exists_gens F
  exact ⟨S, hS, fun K hK z hz => h K hK F.val.toRingHom ⟨z, hz⟩⟩

end Prescribed

section Ray

variable {E : Type} [Field E] [NumberField E]

theorem aut_eq_one (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S.Finite) (F : Type) [Field F] [NumberField F]
    [Algebra E F] (h : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S → IsFrob F v 1) (σ : F ≃ₐ[E] F) : σ = 1 := by
  by_contra hσ
  obtain ⟨T, hT, H⟩ := GlobalTheory.T.exists_two_primes_same_norm_of_trivial_frobenius E F σ hσ
  choose P Q hne hP hQ nP nQ using fun v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S ∪ T} =>
    H v.1 (fun hv => v.2 (Or.inr hv)) (h v.1 fun hv => v.2 (Or.inl hv))
  let f : {v : HeightOneSpectrum (𝓞 E) // v ∉ S ∪ T} × Bool → HeightOneSpectrum (𝓞 F) :=
    fun x => bif x.2 then P x.1 else Q x.1
  have ho : ∀ x, (f x).asIdeal.under (𝓞 E) = x.1.1.asIdeal := by
    rintro ⟨v, _ | _⟩
    exacts [(hQ v).over.symm, (hP v).over.symm]
  refine _root_.GlobalTheory.Mem.ZetaPole.not_injective_double_primes E F _ (hS.union hT) f ?_ ?_
  · rintro ⟨v, b⟩ ⟨w, c⟩ e
    obtain rfl : v = w := Subtype.ext (HeightOneSpectrum.ext ((ho (v, b)).symm.trans (by rw [e]; exact ho (w, c))))
    rcases b with _ | _ <;> rcases c with _ | _
    exacts [rfl, absurd e.symm (hne v), absurd e (hne v), rfl]
  · rintro ⟨v, _ | _⟩
    exacts [nQ v, nP v]

set_option maxHeartbeats 16000000 in
theorem rootOne_mem_ray [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ) {n p : ℕ} (hn : n ≠ 0) (hp : p ∣ n)
    {M : IntermediateField ℚ ℂ} (hM : IsRayFieldIn φ (natIdeal E n) M) : rootOne p ∈ M := by
  classical
  have hp0 : p ≠ 0 := ne_zero_of_dvd_ne_zero hn hp
  have := hM.numberField
  obtain ⟨SM, hSM, hle⟩ := exists_gens_le M
  obtain ⟨L, hfd, hgal, hS, -, -⟩ := GlobalTheory.exists_galois_subfield_conj_stable (insert (rootOne p) SM) (by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    exacts [isAlgebraic_exp p, hSM z hz])
  have hML : M ≤ L := hle L fun z hz => hS z (Finset.mem_insert_of_mem hz)
  have : NumberField L := {}
  let := algOf φ M hM.emb_mem
  let := algOf φ L fun x => hML (hM.emb_mem x)
  let : Algebra M L := (IntermediateField.inclusion hML).toRingHom.toAlgebra
  have : IsScalarTower E M L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L
  have hq : natIdeal E n ≤ Ideal.span {(p : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hp)
  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ natIdeal E n}.Finite :=
    Ideal.finite_factors (natIdeal_ne_bot hn)
  obtain ⟨x, hx⟩ := GlobalTheory.T.rootsOfUnity_mem_rayClassField_of_multiple E M L _ p hp0 hq hM.isRayField
    (_root_.GlobalTheory.Mem.FieldsEx.closure_frob_eq_top E L _ hfin fun F _ _ _ => aut_eq_one _ hfin F) (_root_.GlobalTheory.Mem.RayNorm.absNorm_modEq_one E _ p hq)
    ⟨rootOne p, hS _ (Finset.mem_insert_self _ _)⟩
    (Subtype.ext (Complex.isPrimitiveRoot_exp p hp0).pow_eq_one)
  have e : (x : ℂ) = rootOne p := congrArg Subtype.val hx
  exact e ▸ x.2

theorem valueField_le [IsGalois ℚ E] [_root_.NumberField.IsTotallyComplex E] (φ₀ : E →+* ℂ) {𝔮 : Ideal (𝓞 E)} (h𝔮 : 𝔮 ≠ ⊥)
    {M : IntermediateField ℚ ℂ} [NumberField M] (hM : IsRayFieldIn φ₀ 𝔮 M) {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar E) (n : I → ℤ) (r : ℤ)
    (hi : χ.HasInf φ n) (he : ∀ i, Even (n i - r)) (hu : ∀ v, ¬ v.asIdeal ∣ 𝔮 → χ.UnrAt v) (ht : ∀ v, χ.TameAt v) :
    valueField χ ((r : ℝ) / 2) ≤ kummerField φ₀ (degOver φ₀ M hM.emb_mem) := by
  classical
  rw [valueField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨v, hv, rfl⟩
  let := algOf φ₀ M hM.emb_mem
  obtain ⟨k, hk, hk1⟩ := GlobalTheory.T.exists_generator_pow_prime_one_mod_modulus E 𝔮 _ h𝔮 (_root_.GlobalTheory.Mem.Fld.RayExp.pow_finrank_principal E M 𝔮 hM.isRayField) v
  have hfin := Ideal.finite_factors h𝔮
  refine _root_.GlobalTheory.Mem.FieldsEx.valTw_mem_kummerField E φ₀ I φ hφ χ n r hi he v _ k hk
    (_root_.GlobalTheory.Mem.ValPow.inf_mul_val_pow E χ (hfin.toFinset.erase v) (fun w hw => ?_) (fun w _ => ht w) v (Finset.notMem_erase _ _) _ k hk
      fun w hw => ?_)
  · by_cases e : w = v
    · exact e ▸ hv
    · exact hu w fun h => hw (Finset.mem_erase.2 ⟨e, hfin.mem_toFinset.2 h⟩)
  · exact hk1 w (Finset.mem_erase.1 hw).1 (hfin.mem_toFinset.1 (Finset.mem_erase.1 hw).2)

theorem tameAt_of_unrAt {χ : HChar E} {v : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt v) : χ.TameAt v :=
  fun x hx _ => h x hx

end Ray

section Omega

variable {P : Pre} (D : FieldDat P) (C : Chars P)

theorem host_cplx (P : Pre) : IsTotallyComplex P.host.E := by
  have := P.host.isCMField_hostE
  infer_instance

theorem classNumber_dvd_hstar : classNumber P.host.E ∣ D.hstar := by
  let := algOf P.host.φ₀ D.ray D.isRay.emb_mem
  exact _root_.GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank P.host.E D.ray _ (natIdeal_ne_bot (modulus_ne_zero P)) D.isRay.isRayField

theorem kummer_le_V : kummerField P.host.φ₀ (classNumber P.host.E) ≤ D.V :=
  kummerField_mono _ D.hstar_pos.ne' (classNumber_dvd_hstar D)

theorem finite_adjoin_roots {n : ℕ} (hn : n ≠ 0) {a : ℂ} (ha : IsIntegral ℚ a) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ {z : ℂ | z ^ n = a}) := by
  have : Finite {z : ℂ | z ^ n = a} := by
    refine Set.Finite.subset (Polynomial.nthRoots n a).toFinset.finite_toSet fun z hz => ?_
    simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn)] using hz
  refine IntermediateField.finiteDimensional_adjoin fun z hz => IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
  rw [show z ^ n = a from hz]
  exact ha

theorem finite_cycField (N : ℕ) : FiniteDimensional ℚ (cycField N) :=
  IntermediateField.adjoin.finiteDimensional (isAlgebraic_exp N).isIntegral

theorem finite_M' : FiniteDimensional ℚ D.M' := by
  have := D.good.numberField
  have := D.good.isElliptic
  have : (D.curve.baseChange ℂ).IsElliptic := inferInstanceAs (D.curve.map (algebraMap D.jField ℂ)).IsElliptic
  have hfin := _root_.GlobalTheory.finite_torsionCoords (D.curve.baseChange ℂ) 12 (by norm_num)
  have h1 : FiniteDimensional ℚ ℚ⟮sqrtNegNat P.host.d⟯ := IntermediateField.adjoin.finiteDimensional
    (IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast _).neg))
  have h2 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (torsionCoords (D.curve.baseChange ℂ) 12)) := by
    have := hfin.to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z hz =>
      (_root_.GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite D.jField D.curve 12 hfin z hz).isIntegral
  have h3 := finite_adjoin_roots (n := 12) (a := (D.curve.Δ : ℂ)) (by norm_num)
    ((Algebra.IsIntegral.isIntegral (R := ℚ) D.curve.Δ).map D.jField.val)
  unfold FieldDat.M' discField torsionField hilbertField
  infer_instance

theorem finite_Om : FiniteDimensional ℚ D.Om := by
  have h1 := finite_M' D
  have h2 := finite_cycField (rootOrder P)
  have h3 : FiniteDimensional ℚ D.V := GlobalTheory.T.finiteDimensional_kummerFieldOfPowerIdealRoots _ _ _ D.hstar_pos.ne'
  unfold FieldDat.Om
  infer_instance

theorem dvd_card_GL {g r : ℕ} (hg : g.Prime) (hr : 2 ≤ r) : g * (g - 1) ∣ Nat.card (GL (Fin r) (ZMod g)) := by
  have := Fact.mk hg
  rw [Matrix.card_GL_field, ZMod.card]
  refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨r - 1, by omega⟩ : Fin r)))
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  refine ⟨g ^ s, ?_⟩
  show g ^ (s + 2) - g ^ (s + 1) = _
  rw [mul_right_comm, Nat.mul_sub_one]
  congr 1 <;> ring

theorem rootsField_le_Om : rootsField P ≤ D.Om := by
  have hr : 2 ≤ P.R.r := by
    have := P.R.two_le_m
    have := P.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hf : P.R.f ≠ 0 := mul_ne_zero two_ne_zero P.R.ord_pos.ne'
  have hg : ∀ k, P.host.g k * (P.host.g k - 1) ∣ P.restRowsFiniteGroupCard := fun k =>
    ((dvd_card_GL (P.host.g_prime k) hr).trans (dvd_pow_self _ hf)).trans
      (Finset.dvd_prod_of_mem (fun k : Fin 2 => Nat.card (GL (Fin P.R.r) (ZMod (P.host.g k))) ^ P.R.f)
        (Finset.mem_univ k))
  have key : ∀ {N}, N ∣ rootOrder P → cycField N ≤ D.Om := fun h =>
    (cycField_mono (rootOrder_ne_zero P) h).trans D.cycField_le_Om
  have h1 : P.restRowsFiniteGroupCard ∣ rootOrder P := Nat.dvd_lcm_left _ _
  have h2 : 3 ^ 4 * 5 ^ 4 ∣ rootOrder P := Nat.dvd_lcm_right _ _
  exact sup_le (sup_le (sup_le (sup_le (key h1) (key ((hg 0).trans h1))) (key ((hg 1).trans h1)))
    (key ((dvd_mul_right _ _).trans h2))) (key ((dvd_mul_left _ _).trans h2))

theorem KPsi_le_V (j : ℕ) : D.KPsi j ≤ D.V := by
  refine le_trans (sup_le (sup_le (imField_le_kummerField _ _) (cycField_le_kummerField _ _)) ?_) (kummer_le_V D)
  rw [IntermediateField.adjoin_le_iff]
  rintro z ⟨i, hz⟩
  have hγ : (D.basis.γ i : P.host.E) ∈ powIdealElts P.host.E (D.basis.h i) :=
    ⟨(D.basis.γ i).ne_zero, D.basis.c i, by
      rw [← coe_toPrincipalIdeal, ← D.basis.pow_eq i, Units.val_pow_eq_pow_val]; rfl⟩
  refine kummerField_mono _ (classNumber_ne_zero _) (orderOf_dvd_card : D.basis.h i ∣ _) (mem_kummerField _ ?_ hz)
  have hσ : ∀ (σ : P.host.E ≃ₐ[ℚ] P.host.E) {x}, x ∈ powIdealElts P.host.E (D.basis.h i) →
      σ x ∈ powIdealElts P.host.E (D.basis.h i) := fun σ _ hx => map_mem_pow (σ : P.host.E →+* P.host.E) hx
  exact prod_mem_pow _ _ fun g _ => mul_mem_pow (npow_mem_pow (hσ _ hγ) _) (npow_mem_pow (hσ _ (hσ _ hγ)) _)

theorem value_le_V (χ : HChar P.host.E) (n : P.R.Psi → ℤ) (r : ℤ) (hi : χ.HasInf (embPsi P.host) n)
    (he : ∀ i, Even (n i - r)) (hu : ∀ v, (∀ p, p ∣ modulus P → OverP P.host p v → p = 0) → χ.UnrAt v)
    (ht : ∀ v, χ.TameAt v) : valueField χ ((r : ℝ) / 2) ≤ D.V := by
  have := host_cplx P
  have : IsGalois ℚ P.host.E := P.host.hostE_isGalois
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm P.R P.host
  refine valueField_le _ (natIdeal_ne_bot (modulus_ne_zero P)) D.isRay _ hcm.bij χ n r hi he
    (fun v hv => hu v fun p hp ho => absurd ?_ hv) ht
  obtain ⟨k, hk⟩ := hp
  rw [Ideal.dvd_span_singleton, hk, Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ ho

theorem delta_le_V {p : ℕ} (hp : p ∣ modulus P) {χ : HChar P.host.E} (h : IsDelta (H := P.host) p χ) :
    valueField χ 0 ≤ D.V := by
  have := host_cplx P
  obtain ⟨n, hn, ho⟩ := h.fin
  have := value_le_V D χ (fun _ => 0) 0 (fun k => by simp [GlobalTheory.TypeValues.inf_eq_one χ hn ho k]) (fun _ => by simp)
    (fun v hv => h.unr v fun ho => ne_zero_of_dvd_ne_zero (modulus_ne_zero P) hp (hv p hp ho)) h.tame
  simpa using this

theorem pde_dvd (P : Pre) : P.host.pde ∣ modulus P := (dvd_mul_left _ _).mul_right _

theorem pde'_dvd (P : Pre) : P.host.pde' ∣ modulus P := dvd_mul_left _ _

theorem charField_le_Om : charField C ≤ D.Om := by
  refine sup_le (sup_le (sup_le (sup_le (iSup_le fun j => ?_) ?_) ?_) ?_) ?_
  · obtain ⟨n, hn, hi⟩ := (C.isMu0 j).inf
    have hg : ∀ k, P.host.g k ∣ modulus P := fun k => by
      fin_cases k
      · exact ((dvd_mul_right _ _).mul_right _).mul_right _
      · exact ((dvd_mul_left _ _).mul_right _).mul_right _
    have := value_le_V D (C.mu0 j) n 0 hi (fun i => by
        obtain ⟨z, hz⟩ := (P.hc i).e_int j
        have h1 : (n i : ℚ) = 2 * -(P.hc i).e j := hn i
        rw [hz] at h1
        have h2 : n i = 2 * -z := by exact_mod_cast h1
        exact ⟨-z, by rw [h2]; ring⟩)
      (fun v hv => (C.isMu0 j).unr v fun k ho => (P.host.g_prime k).ne_zero (hv _ (hg k) ho)) (C.isMu0 j).tame
    simpa using this.trans D.V_le_Om
  · simpa using (value_le_V D C.eta (fun _ => 1) 1 C.isEta.inf (fun _ => by simp) (fun v _ => C.isEta.unr v)
      fun v => tameAt_of_unrAt (C.isEta.unr v)).trans D.V_le_Om
  · exact (delta_le_V D (pde_dvd P) C.isDel).trans D.V_le_Om
  · exact (delta_le_V D (pde'_dvd P) C.isDel').trans D.V_le_Om
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, a, rfl⟩
    exact rootsField_le_Om D (om_mem_rootsField C k a)

theorem listField_le_Om : listField D C ≤ D.Om :=
  (listField_le_iff D C).2 ⟨D.imField_le_Om, D.M'_le_Om, D.ray_le_Om, rootsField_le_Om D, charField_le_Om D C,
    fun j _ _ => (KPsi_le_V D j).trans D.V_le_Om⟩

end Omega

end GlobalTheory.Mem.FieldsEx

end
