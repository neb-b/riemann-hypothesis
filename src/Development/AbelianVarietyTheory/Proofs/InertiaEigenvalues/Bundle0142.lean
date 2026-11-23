module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerRelIndexIntUnitsNeZero
section
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.StabIdx

theorem relIndex_ne_zero_of_map {G X : Type} [Group G] [Finite X] (H K : Subgroup G) (f : K → X)
    (hf : ∀ a b : K, f a = f b → (a : G)⁻¹ * b ∈ H) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    refine Finite.of_injective (fun q : K ⧸ H.subgroupOf K => f q.out) ?_
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hf _ _ h
  exact Subgroup.index_ne_zero_of_finite

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem mem_stabilizer_of {g : A} (L : stLat O E g) (t : Aˣ)
    (h1 : ∀ y ∈ (L : Submodule O A), (t : A) * y ∈ (L : Submodule O A))
    (h2 : ∀ y ∈ (L : Submodule O A), ((t⁻¹ : Aˣ) : A) * y ∈ (L : Submodule O A)) :
    t ∈ MulAction.stabilizer Aˣ L := by
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  rw [stLat_smul_val]
  ext x
  rw [mem_mulLat_iff]
  constructor
  · intro hx
    have := h1 _ hx
    rwa [← mul_assoc, Units.mul_inv, one_mul] at this
  · intro hx
    exact h2 _ hx

theorem finite_quotient_span [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {c : O} (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    (inferInstance : Finite (IsLocalRing.ResidueField O))
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal O)) n
  rwa [hm, Ideal.span_singleton_pow, ← hn] at this

variable [IsDomain O] [Algebra O E] [IsFractionRing O E] [IsScalarTower O E A]

theorem exists_smul_mul_mem (C L : Submodule O A) (hC : C.FG) (hL : IsLat O E L) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ C, ∀ y ∈ L, c • (x * y) ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hC
  obtain ⟨t, ht⟩ := hL.1
  have hex : ∀ p : A × A, ∃ r : O, r ≠ 0 ∧ r • (p.1 * p.2) ∈ L := fun p =>
    ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.exists_smul_mem_of_mem_span (C := E) L (by rw [hL.2]; trivial)
  choose r hr0 hrm using hex
  refine ⟨∏ p ∈ s ×ˢ t, r p, Finset.prod_ne_zero_iff.2 fun p _ => hr0 p, ?_⟩
  have hgen : ∀ a ∈ s, ∀ b ∈ t, (∏ p ∈ s ×ˢ t, r p) • (a * b) ∈ L := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem r (Finset.mem_product.2 ⟨ha, hb⟩ : (a, b) ∈ s ×ˢ t)
    rw [hk, mul_comm, mul_smul]
    exact L.smul_mem _ (hrm (a, b))
  intro x hx y hy
  rw [← ht] at hy
  induction hy using Submodule.span_induction with
  | mem b hb =>
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem a ha => exact hgen a ha b hb
    | zero => simp
    | add u v _ _ hu hv => rw [add_mul, smul_add]; exact L.add_mem hu hv
    | smul o u _ hu => rw [smul_mul_assoc, smul_comm]; exact L.smul_mem _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, smul_add]; exact L.add_mem hu hv
  | smul o u _ hu => rw [mul_smul_comm, smul_comm]; exact L.smul_mem _ hu

theorem relIndex_ne_zero_of_fg [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {g : A} (hC : (Subalgebra.toSubmodule (integralClosure O A)).FG) (L : stLat O E g) :
    (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  classical
  set C := Subalgebra.toSubmodule (integralClosure O A) with hCdef
  obtain ⟨c, hc0, hcL⟩ := exists_smul_mul_mem (E := E) C (L : Submodule O A) hC L.2.1
  haveI := finite_quotient_span hc0
  haveI : Finite (C ⧸ (⊤ : Submodule O C)) := by
    haveI : Subsingleton (C ⧸ (⊤ : Submodule O C)) := Submodule.Quotient.subsingleton_iff.2 rfl
    infer_instance
  haveI : Finite (C ⧸ Ideal.span {c} • (⊤ : Submodule O C)) :=
    Submodule.finite_quotient_smul _ ((Submodule.fg_top C).2 hC)
  have hmemC : ∀ x : A, IsIntegral O x → x ∈ C := fun x hx => hx
  let f : intUnits O A → C ⧸ Ideal.span {c} • (⊤ : Submodule O C) := fun t =>
    Submodule.Quotient.mk ⟨((t : Aˣ) : A), hmemC _ t.2.1⟩
  refine relIndex_ne_zero_of_map _ _ f fun a b hab => ?_
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hab
  obtain ⟨n, -, hn⟩ := hab
  have hn' : c • (n : A) = ((a : Aˣ) : A) - ((b : Aˣ) : A) := by
    have := congrArg Subtype.val hn
    simpa using this
  have ha : ((a : Aˣ)⁻¹ : Aˣ).val * (a : Aˣ).val = 1 := Units.inv_mul _
  have hb : ((b : Aˣ)⁻¹ : Aˣ).val * (b : Aˣ).val = 1 := Units.inv_mul _
  have hna : ((a : Aˣ)⁻¹ : Aˣ).val * (n : A) ∈ C := hmemC _ (a.2.2.mul n.2)
  have hnb : ((b : Aˣ)⁻¹ : Aˣ).val * (n : A) ∈ C := hmemC _ (b.2.2.mul n.2)
  apply mem_stabilizer_of L
  · intro y hy
    have e : (((a : Aˣ)⁻¹ * (b : Aˣ) : Aˣ) : A) * y =
        y - c • ((((a : Aˣ)⁻¹ : Aˣ).val * (n : A)) * y) := by
      rw [Units.val_mul]
      rw [Algebra.smul_def] at hn' ⊢
      linear_combination (((a : Aˣ)⁻¹ : Aˣ).val * y) * hn' + y * ha
    rw [e]
    exact L.1.sub_mem hy (hcL _ hna _ hy)
  · intro y hy
    have e : ((((a : Aˣ)⁻¹ * (b : Aˣ))⁻¹ : Aˣ) : A) * y =
        y + c • ((((b : Aˣ)⁻¹ : Aˣ).val * (n : A)) * y) := by
      rw [mul_inv_rev, inv_inv, Units.val_mul]
      rw [Algebra.smul_def] at hn' ⊢
      linear_combination (-(((b : Aˣ)⁻¹ : Aˣ).val * y)) * hn' + y * hb
    rw [e]
    exact L.1.add_mem hy (hcL _ hnb _ hy)

theorem stabilizer_relIndex_intUnits_ne_zero : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A]
    [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable →
    ∀ L : stLat O E g, (MulAction.stabilizer Aˣ L).relIndex (intUnits O A) ≠ 0 := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ _ g hg L
  haveI := GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft E A g hg
  exact relIndex_ne_zero_of_fg (_root_.GlobalTheory.IntegralClosureFG.integralClosure_fg O E A) L

end GlobalTheory.UnitLemma.StabIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusModIntegralUnitsStructureAndIntegrality
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem torus_mod_intUnits_structure : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by
  intro K B hL a ha
  have hred : IsReduced B.A := _root_.GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg K B hL
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  have hv : ∀ m : MaximalSpectrum B.A, ∃ v : (B.A ⧸ m.asIdeal)ˣ →* Multiplicative ℤ,
      Function.Surjective v ∧ ∀ x : (B.A ⧸ m.asIdeal)ˣ,
        IsIntegral K.O (x : B.A ⧸ m.asIdeal) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
    intro m
    haveI := m.isMaximal
    letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    haveI : FiniteDimensional K.E (B.A ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E m.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K.E m.asIdeal)
    exact _root_.GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff K (B.A ⧸ m.asIdeal)
  choose v hvs hvi using hv
  let w : MaximalSpectrum B.A → B.Aˣ →* Multiplicative ℤ := fun m =>
    (v m).comp (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal))
  have hw : ∀ m (x : B.Aˣ), IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (x : B.A)) ↔
      0 ≤ Multiplicative.toAdd (w m x) := fun m x =>
    hvi m (Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) x)
  have hP : ∀ x : B.Aˣ, IsIntegral K.O (x : B.A) ↔ ∀ m, 0 ≤ Multiplicative.toAdd (w m x) := by
    intro x
    rw [GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue K B hred]
    exact forall_congr' fun m => hw m x
  let τ : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)
  have hτ : ∀ x, τ (τ x) = x := fun x => Units.ext (B.σ_σ _)
  have hT : ∀ t, t ∈ B.T ↔ t * τ t = 1 := by
    intro t
    rw [Units.ext_iff]
    rfl
  let s : MaximalSpectrum B.A → MaximalSpectrum B.A := fun m =>
    ⟨m.asIdeal.comap B.σ, Ideal.comap_isMaximal_of_surjective B.σ B.σ.surjective⟩
  have hs : ∀ m, s (s m) = m := by
    intro m
    ext y
    show B.σ (B.σ y) ∈ m.asIdeal ↔ y ∈ m.asIdeal
    rw [B.σ_σ]
  have hswap : ∀ m x, 0 ≤ Multiplicative.toAdd (w (s m) x) ↔ 0 ≤ Multiplicative.toAdd (w m (τ x)) := by
    intro m x
    rw [← hw, ← hw]
    exact _root_.GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff K B m x
  have hsupp : ∀ m (n : ℤ), ∃ y : B.Aˣ, w m y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ m → w j y = 1 := by
    intro m n
    obtain ⟨z, hz⟩ := hvs m (Multiplicative.ofAdd n)
    obtain ⟨y, hy1, hy2⟩ := _root_.GlobalTheory.UnitLemma.unit_prescribed_residue K B hred m (z : B.A ⧸ m.asIdeal) z.ne_zero
    refine ⟨y, ?_, fun j hj => ?_⟩
    · have : Units.map (Ideal.Quotient.mk m.asIdeal : B.A →* B.A ⧸ m.asIdeal) y = z := Units.ext hy1
      show v m _ = _
      rw [this, hz]
    · have : Units.map (Ideal.Quotient.mk j.asIdeal : B.A →* B.A ⧸ j.asIdeal) y = 1 := Units.ext (hy2 j hj)
      show v j _ = _
      rw [this, map_one]
  have hne : algebraMap K.O K.E a ≠ 0 := by
    intro h
    exact ha.1 (IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm))
  let α : B.Aˣ := Units.map (algebraMap K.E B.A : K.E →* B.A) (Units.mk0 _ hne)
  have hαv : (α : B.A) = algebraMap K.O B.A a := (IsScalarTower.algebraMap_apply K.O K.E B.A a).symm
  have hτα : τ α = α := by
    apply Units.ext
    show B.σ (algebraMap K.E B.A (algebraMap K.O K.E a)) = algebraMap K.E B.A (algebraMap K.O K.E a)
    rw [B.σ_alg, ha.2.2]
  have hαpos : ∀ m, 0 < Multiplicative.toAdd (w m α) := by
    intro m
    by_contra hle
    push_neg at hle
    have h1 : 0 ≤ Multiplicative.toAdd (w m α⁻¹) := by
      rw [map_inv, toAdd_inv]
      linarith
    rw [← hw] at h1
    apply _root_.GlobalTheory.NotIntegral.inv_small_not_integral K B a ha m
    convert h1 using 1
    show _ = Ideal.Quotient.mk m.asIdeal (algebraMap K.E B.A (algebraMap K.O K.E a)⁻¹)
    rw [Ideal.Quotient.mk_algebraMap]
  obtain ⟨r, e, he1, he2, he3⟩ := _root_.GlobalTheory.involution_pair_representatives (MaximalSpectrum B.A) s hs
  refine ⟨r, ((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp B.T.subtype, fun j => (Multiplicative.toAdd (w (e j) α)).toNat,
    _root_.GlobalTheory.UnitLemma.valsAt_torus_surjective B.Aˣ τ hτ B.T hT _ s w hswap hsupp r e he1 he2, fun t => ?_, fun j => ?_, fun t k => ?_⟩
  · rw [GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff B.Aˣ τ B.T hT _ s w hswap r e he3]
    show _ ↔ IsIntegral K.O ((t : B.Aˣ) : B.A) ∧ IsIntegral K.O (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A)
    rw [hP, hP]
    constructor
    · intro h
      exact ⟨fun m => (h m).ge, fun m => by rw [map_inv, toAdd_inv, h m, neg_zero]⟩
    · rintro ⟨ha1, ha2⟩ m
      have := ha2 m
      rw [map_inv, toAdd_inv] at this
      linarith [ha1 m]
  · exact Int.lt_toNat.mpr (hαpos (e j))
  · rw [← _root_.GlobalTheory.TorusInteg.torus_integral_iff B.Aˣ τ B.T hT _ s w hswap r e he3 α hτα hαpos, ← hP]
    congr 2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hαv]

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAlmostOntoOfLevels
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.AlmostTrace

variable {l : ℕ} [Fact l.Prime]

theorem Ks_le_Kinf (K : FinExt l) (i : ℕ) : Ks K i ≤ Kinf K := by
  unfold Ks Kinf
  exact sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] {x : Om l | x ^ l ^ i = 1}
    {x : Om l | ∃ j : ℕ, x ^ l ^ j = 1} fun x hx => (⟨i, hx⟩ : ∃ j : ℕ, x ^ l ^ j = 1)) _

theorem Ks_mono (K : FinExt l) : Monotone (Ks K) := by
  intro i j hij
  unfold Ks
  refine sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] {x : Om l | x ^ l ^ i = 1}
    {x : Om l | x ^ l ^ j = 1} fun x hx => ?_) _
  obtain ⟨c, hc⟩ := pow_dvd_pow l hij
  have hx' : x ^ l ^ i = 1 := hx
  show x ^ l ^ j = 1
  rw [hc, pow_mul, hx', one_pow]

theorem Kinf_eq_iSup (K : FinExt l) : Kinf K = ⨆ i, Ks K i := by
  refine le_antisymm ?_ (iSup_le fun i => Ks_le_Kinf K i)
  have h0 : K0 K ≤ Ks K 0 := by
    unfold Ks
    exact le_sup_left
  unfold Kinf
  refine sup_le (h0.trans (le_iSup (Ks K) 0)) ?_
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨j, hj⟩
  have hx : x ∈ Ks K j := by
    unfold Ks
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ j = 1} ≤ _)
      (IntermediateField.subset_adjoin _ _ hj)
  exact le_iSup (Ks K) j hx

theorem exists_mem_Ks (K : FinExt l) {x : Om l} (hx : x ∈ Kinf K) : ∃ i, x ∈ Ks K i := by
  rw [Kinf_eq_iSup] at hx
  have h : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hx
  rw [IntermediateField.coe_iSup_of_directed (Ks_mono K).directed_le, Set.mem_iUnion] at h
  exact h

theorem Hinf_le_Gj (K : FinExt l) (i : ℕ) : Hinf K ≤ Gj K i := by
  unfold Hinf Gj
  exact IntermediateField.fixingSubgroup_antitone (Ks_le_Kinf K i)

theorem exists_Gj_subset (K : FinExt l) {U : Set (GQ l)} (hU : IsOpen U)
    (hH : (Hinf K : Set (GQ l)) ⊆ U) : ∃ i₀, ∀ i ≥ i₀, (Gj K i : Set (GQ l)) ⊆ U := by
  have hcl : ∀ i, IsClosed ((Gj K i : Set (GQ l))) := fun i =>
    InfiniteGalois.fixingSubgroup_isClosed (Ks K i)
  have hanti : Antitone fun i => ((Gj K i : Set (GQ l))) := fun i j hij =>
    IntermediateField.fixingSubgroup_antitone (Ks_mono K hij)
  have hinter : Uᶜ ∩ ⋂ i, (Gj K i : Set (GQ l)) = ∅ := by
    ext σ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hσU, hσ⟩
    apply hσU
    apply hH
    show σ ∈ (Kinf K).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_Ks K hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Set.mem_iInter.1 hσ i) x hi
  obtain ⟨i₀, hi₀⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun i => (Gj K i : Set (GQ l))) hcl (Set.disjoint_iff_inter_eq_empty.mpr hinter) hanti.directed_ge
  refine ⟨i₀, fun i hi σ hσ => ?_⟩
  by_contra hσU
  have hmem : σ ∈ Uᶜ ∩ (Gj K i₀ : Set (GQ l)) := ⟨hσU, hanti hi hσ⟩
  exact Set.disjoint_left.1 hi₀ hmem.1 hmem.2

theorem sum_mem_Kinf (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) {b : Om l} (hb : b ∈ L) :
    ∑ s ∈ S, s b ∈ Kinf K := by
  classical
  rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
  intro h hh
  have hex : ∀ s ∈ S, ∃ t, t ∈ S ∧ t⁻¹ * (h * s) ∈ L.fixingSubgroup := fun s hs =>
    (hrep (h * s) (mul_mem hh (hS s hs))).exists
  choose! φ hφS hφF using hex
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_nbij φ hφS ?_ ?_ ?_
  · intro s₁ hs₁ s₂ hs₂ he
    have h₁ := hφF s₁ hs₁
    have h₂ := hφF s₂ hs₂
    rw [he] at h₁
    have hm : s₁⁻¹ * s₂ ∈ L.fixingSubgroup := by
      have := mul_mem (inv_mem h₁) h₂
      rwa [show ((φ s₂)⁻¹ * (h * s₁))⁻¹ * ((φ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ by group] at this
    exact (hrep s₂ (hS s₂ hs₂)).unique ⟨hs₁, hm⟩ ⟨hs₂, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro t ht
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep (h⁻¹ * t) (mul_mem (inv_mem hh) (hS t ht))
    refine ⟨s, Finset.mem_coe.2 hs, ?_⟩
    have hm : t⁻¹ * (h * s) ∈ L.fixingSubgroup := by
      have := inv_mem hsm
      rwa [show (s⁻¹ * (h⁻¹ * t))⁻¹ = t⁻¹ * (h * s) by group] at this
    exact (hrep (h * s) (mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφF s hs⟩ ⟨ht, hm⟩
  · intro s hs
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hφF s hs) b hb
    have key : (φ s) (((φ s)⁻¹ * (h * s)) b) = h (s b) := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel_left, AlgEquiv.mul_apply]
    rw [hfix] at key
    exact key.symm

theorem exists_finite_level (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) :
    ∃ L' : FinExt l, L'.1 ≤ L ∧ ∃ i₀, ∀ i ≥ i₀, ∀ h ∈ Gj K i,
      ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup := by
  classical
  have hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ x ∈ L, (s⁻¹ * t) x ≠ x := by
    intro s hs t ht hst
    by_contra hne
    push Not at hne
    apply hst
    have hmem : s⁻¹ * t ∈ L.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).2 hne
    exact (hrep t (hS t ht)).unique ⟨hs, hmem⟩ ⟨ht, by rw [inv_mul_cancel]; exact one_mem _⟩
  choose! xf hxL hxne using hsep
  let T : Finset (Om l) := ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => xf p.1 p.2
  have hTmem : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → xf s t ∈ (T : Set (Om l)) := by
    intro s hs t ht hst
    simp only [T, Finset.coe_image, Finset.coe_filter]
    exact ⟨(s, t), ⟨Finset.mem_product.2 ⟨hs, ht⟩, hst⟩, rfl⟩
  let L' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (T : Set (Om l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩
  have hL'L : L'.1 ≤ L := by
    show IntermediateField.adjoin ℚ_[l] (T : Set (Om l)) ≤ L
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [T, Finset.coe_image, Finset.coe_filter, Set.mem_image] at hx
    obtain ⟨p, ⟨hp, hpne⟩, rfl⟩ := hx
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    exact hxL p.1 hp1 p.2 hp2 hpne
  have : FiniteDimensional ℚ_[l] L'.1 := L'.2
  let U : Set (GQ l) := ⋃ s ∈ S, {σ | s⁻¹ * σ ∈ L'.1.fixingSubgroup}
  have hUo : IsOpen U := isOpen_biUnion fun s _ =>
    (IntermediateField.fixingSubgroup_isOpen L'.1).preimage (continuous_const.mul continuous_id)
  have hHU : (Hinf K : Set (GQ l)) ⊆ U := by
    intro σ hσ
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep σ hσ
    exact Set.mem_biUnion hs (IntermediateField.fixingSubgroup_antitone hL'L hsm)
  obtain ⟨i₀, hi₀⟩ := exists_Gj_subset K hUo hHU
  refine ⟨L', hL'L, i₀, fun i hi h hh => ?_⟩
  obtain ⟨s, hs, hsm⟩ := Set.mem_iUnion₂.1 (hi₀ i hi hh)
  have hsG : s⁻¹ * h ∈ Gj K i := mul_mem (inv_mem (Hinf_le_Gj K i (hS s hs))) hh
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hsm, hsG⟩
  · rintro t ⟨ht, htm⟩
    by_contra hts
    have htm' : t⁻¹ * h ∈ L'.1.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone le_sup_left htm
    have hm : t⁻¹ * s ∈ L'.1.fixingSubgroup := by
      have := mul_mem htm' (inv_mem hsm)
      rwa [show t⁻¹ * h * (s⁻¹ * h)⁻¹ = t⁻¹ * s by group] at this
    have hxT : xf t s ∈ L'.1 := IntermediateField.subset_adjoin _ _ (hTmem t ht s hs hts)
    exact hxne t ht s hs hts ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hm _ hxT)

theorem trace_almost_onto_of_levels
    (hd : ∀ (K L' : FinExt l) (ε : ℝ), 0 < ε → ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ S : Finset (GQ l),
      (∀ s ∈ S, s ∈ Gj K i) →
      (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup) →
      ∃ b : Om l, b ∈ L'.1 ⊔ Ks K i ∧ ‖b‖ ≤ 1 ∧ 1 - ε ≤ ‖∑ s ∈ S, s b‖)
    (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, zero_mem _, by simp, by simp [ha0]⟩
  obtain ⟨L', hL'L, i₀, hi₀⟩ := exists_finite_level K L S hS hrep
  have hε : 0 < 1 - ‖a‖ := by linarith
  obtain ⟨i₁, hi₁⟩ := hd K L' (1 - ‖a‖) hε
  obtain ⟨b₀, hb₀, hb₀1, htr⟩ := hi₁ (max i₀ i₁) (le_max_right _ _) S
    (fun s hs => Hinf_le_Gj K _ (hS s hs)) (hi₀ (max i₀ i₁) (le_max_left _ _))
  have hb₀L : b₀ ∈ L := (sup_le hL'L ((Ks_le_Kinf K _).trans hKL)) hb₀
  have htK : ∑ s ∈ S, s b₀ ∈ Kinf K := sum_mem_Kinf K L S hS hrep hb₀L
  set t := ∑ s ∈ S, s b₀ with ht
  have hta : ‖a‖ ≤ ‖t‖ := by linarith
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hta
    exact ha0 (norm_le_zero_iff.1 hta)
  have hc : a / t ∈ Kinf K := div_mem ha htK
  refine ⟨a / t * b₀, mul_mem (hKL hc) hb₀L, ?_, ?_⟩
  · rw [norm_mul, norm_div]
    have h1 : ‖a‖ / ‖t‖ ≤ 1 := (div_le_one (norm_pos_iff.2 ht0)).2 hta
    calc ‖a‖ / ‖t‖ * ‖b₀‖ ≤ 1 * 1 := mul_le_mul h1 hb₀1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have hfix : ∀ s ∈ S, s (a / t) = a / t := fun s hs =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hS s hs) _ hc
    rw [Finset.sum_congr rfl fun s hs => by rw [map_mul, hfix s hs], ← Finset.mul_sum,
      ← ht, div_mul_cancel₀ a ht0]

end GlobalTheory.Cyc.AlmostTrace
end
end

