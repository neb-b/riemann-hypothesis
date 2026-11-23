module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeNormalFormUnipotent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleRepresentativesFiniteLevelCosets
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxFin

open GlobalTheory.Mem.LevFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_classes {N q : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (j : ℕ) :
    ∃ (ι : Type) (_ : Finite ι) (f : (Sp E N ≃ₗ[E] Sp E N) → ι), ∀ h h' : Sp E N ≃ₗ[E] Sp E N,
      (∀ x ∈ LocE.sclLat P q N e, h⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h x ∈ LocE.sclLat P q N e) →
      (∀ x ∈ LocE.sclLat P q N e, h'⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h' x ∈ LocE.sclLat P q N e) →
      f h = f h' → ∀ x ∈ LocE.sclLat P q N e, (q : E)⁻¹ • ((h⁻¹ * h') x - x) ∈ LocE.sclLat P q N e := by
  classical
  have hc : ((q ^ (j + 1) : ℕ) : E) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hq
  have hq' : ((q ^ (j + 1) : ℕ) : 𝓞 E) ≠ 0 := fun h0 => hc (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have hfin : Finite (𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa only [Ne, Ideal.span_singleton_eq_bot] using hq')
  have hz : ∀ l : ℕ, (q : E) ^ e l ≠ 0 := fun l => zpow_ne_zero _ hq
  have he : ∀ i : Fin N, (Pi.single i ((q : E) ^ e i.1) : Sp E N) ∈ LocE.sclLat P q N e := by
    intro i
    rw [GlobalTheory.CongLevel.mem_sclLat]
    intro l
    rw [Pi.single_apply]
    split_ifs with hl
    · rw [hl, inv_mul_cancel₀ (hz _)]
      exact GlobalTheory.GO.ChRoot.intAt_one'
    · rw [mul_zero]
      exact GlobalTheory.GO.ChRoot.intAt_zero'
  let m : (Sp E N ≃ₗ[E] Sp E N) → Fin N → Fin N → E :=
    fun h i l => ((q : E) ^ e l.1)⁻¹ * ((q : E) ^ j * h (Pi.single i ((q : E) ^ e i.1)) l)
  have hex : ∀ a : E, ∃ r : 𝓞 E, IntAt P a → IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (a - algebraMap (𝓞 E) E r)) := by
    intro a
    by_cases ha : IntAt P a
    · obtain ⟨r, hr⟩ := exists_int_congr hc ha
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose r hr using hex
  refine ⟨Fin N → Fin N → 𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}, inferInstance,
    fun h i l => Ideal.Quotient.mk _ (r (m h i l)), fun a b ha hb hab x hx => ?_⟩
  have hma : ∀ i l, IntAt P (m a i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (ha _ (he i)).2 l
  have hmb : ∀ i l, IntAt P (m b i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (hb _ (he i)).2 l
  have h1 : ∀ i l, IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    intro i l
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun hab i) l))
    have ht' := congrArg (algebraMap (𝓞 E) E) ht
    simp only [map_mul, map_natCast, map_sub] at ht'
    have := ((hr _ (hmb i l)).add (intAt_neg (hr _ (hma i l)))).add (intAt_neg (IntAt.coe P t))
    convert this using 1
    generalize ((q ^ (j + 1) : ℕ) : E) = c at *
    field_simp
    linear_combination ht'
  have e1 : (q : E)⁻¹ • ((a⁻¹ * b) x - x) = a⁻¹ ((q : E)⁻¹ • (b x - a x)) := by
    rw [map_smul, map_sub, show a⁻¹ (a x) = x from LinearEquiv.symm_apply_apply _ x]
    rfl
  rw [e1]
  refine (ha _ ?_).1
  rw [GlobalTheory.CongLevel.mem_sclLat] at hx ⊢
  intro l
  have ex : x = ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) • (Pi.single i ((q : E) ^ e i.1) : Sp E N) := by
    funext l
    have := hz l.1
    simp [Finset.sum_apply, Pi.single_apply]
    field_simp
  have e2 : ((q : E) ^ e l.1)⁻¹ * ((q : E)⁻¹ • (b x - a x)) l =
      ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) * (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    conv_lhs => rw [ex]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      Finset.mul_sum, m]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hz l.1
    have := hz i.1
    push_cast
    field_simp
    ring
  rw [e2]
  exact Finset.sum_induction _ (IntAt P) (fun _ _ => IntAt.add) GlobalTheory.GO.ChRoot.intAt_zero' fun i _ =>
    (hx i).mul (h1 i l)

theorem exists_finite_index_of_adm_cosets : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), ∃ (ι : Type) (_ : Finite ι) (f : AutY X R j → ι), ∀ h h' : AutY X R j, admitted Pr j P h → admitted Pr j P h' → f h = f h' → h⁻¹ * h' ∈ Jat (Pr := Pr) sharp j P := by
  intro X Pr R sharp j P
  classical
  have hq := qOf_ne P
  have hb : ∀ h : AutY X R j, admitted Pr j P h → ∀ x ∈ lamYat (Pr := Pr) (R := R) j P,
      h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧ ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P := by
    intro h hh
    by_cases hP : P ∈ Pr.vGs
    · have hs := hh.1 hP
      intro x hx
      refine ⟨((inv_mem hs) x).2 hx, ?_⟩
      rw [← Nat.cast_pow]
      exact natCast_smul_mem _ _ ((hs x).2 hx)
    · exact (between_iff hP h).2 (hh.2 hP)
  obtain ⟨ι, hι, f, hf⟩ := exists_classes (P := P) (N := R.N j + cOf R j) hq
    (LocE.scE (R.N j) (if P ∈ Pr.vGs then fun i => i + 1 else 0)) j
  refine ⟨ι, hι, f, fun h h' hh hh' e => ?_⟩
  have h1 := hf h h' (hb h hh) (hb h' hh') e
  have h2 := hf h' h (hb h' hh') (hb h hh) e.symm
  refine mem_Jat _ _ _ _ (stab_of_cong hq _ _ h1 ?_) h1
  rw [mul_inv_rev, inv_inv]
  exact h2

end GlobalTheory.Mem.Col2.IdxFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineEigenvalueEqOneOfBoxSumNeZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero

def periods {V K : Type} [AddCommGroup V] (f : V → K) : AddSubgroup V where
  carrier := {u | ∀ t, f (t + u) = f t}
  zero_mem' := fun t => by simp
  add_mem' := fun {a b} ha hb t => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha t => by rw [← ha (t + -a)]; simp

theorem eigen_eq_one_of_reps {V K : Type} [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (L : AddSubgroup V)
    (S : Finset V) (hf : ∀ v, ∀ u ∈ L, f (v + u) = f v) (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ L → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ L) (T : V ≃+ V) (b : V) (χ : K) (hT : ∀ t, f (T t + b) = χ * f t)
    (hS : ∑ s ∈ S, f s ≠ 0) : χ = 1 := by
  classical
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hsurj : ∀ v, ∃ t, T t + b = v := fun v => ⟨T.symm (v - b), by simp⟩
  have hχ : χ ≠ 0 := by
    rintro rfl
    obtain ⟨t, rfl⟩ := hsurj t₀
    exact ht₀ (by rw [hT, zero_mul])
  set M := periods f with hM
  have hMf : ∀ v, ∀ u ∈ M, f (v + u) = f v := fun v u hu => hu v
  have hLM : L ≤ M := fun u hu t => hf t u hu
  have hTM : ∀ u, T u ∈ M ↔ u ∈ M := fun u => by
    have e : ∀ t, f (T t + b + T u) = χ * f (t + u) := fun t => by
      rw [← hT, map_add (f := _)]; congr 1; abel
    constructor
    · intro h t
      apply mul_left_cancel₀ hχ
      rw [← e, hMf _ _ h, hT]
    · intro h v
      obtain ⟨t, rfl⟩ := hsurj v
      rw [e, hMf _ _ h, hT]
  have hmap : M.map (T : V →+ V) = M := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hTM u).2 hu
    · intro hv
      exact ⟨T.symm v, (hTM _).1 (by simpa using hv), by simp⟩
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := fun v => by
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    simpa using hMf v _ h
  let S' : Finset V := S.image fun s => (QuotientAddGroup.mk s : V ⧸ M).out
  have hinj' : ∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ M → s = s' := fun s hs s' hs' h => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 hs'
    have := QuotientAddGroup.eq_iff_sub_mem.2 h
    simp only [QuotientAddGroup.out_eq'] at this
    rw [this]
  have hcov' : ∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ M := fun v hv => by
    obtain ⟨s, hs, e⟩ := hcov v hv
    refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', QuotientAddGroup.eq_iff_sub_mem]
    exact hLM e
  have i1 : M.relIndex L ≠ 0 := by rw [AddSubgroup.relIndex_eq_one.2 hLM]; exact one_ne_zero
  have i2 : L.relIndex M ≠ 0 :=
    boxSum_ne_zero_invariant_affineChange.relIndex_ne_zero_of_cover L M (S.image fun s => s - t₀) fun k hk => by
      obtain ⟨s, hs, e⟩ := hcov (t₀ + k) (by rwa [hMf _ _ hk])
      refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
      convert e using 1
      abel
  have h1 := (sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff V K f L M S S' i1 i2 hf hMf hinj hcov hinj' hcov').1 hS
  have h2 := sum_coset_reps_ne_zero_iff_commensurable.finsum_quot_eq f M M S' le_rfl (by simp) hMf hinj' hcov'
  rw [AddSubgroup.relIndex_self, Nat.cast_one, one_mul] at h2
  rw [← h2] at h1
  let e : V ⧸ M ≃ V ⧸ M := (QuotientAddGroup.congr M M T hmap).toEquiv.trans (Equiv.addRight (QuotientAddGroup.mk b))
  have he : ∀ c : V ⧸ M, f (e c).out = χ * f c.out := fun c => by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective c
    have : e (QuotientAddGroup.mk v) = QuotientAddGroup.mk (T v + b) := rfl
    rw [this, hout, hout, hT]
  have h3 : ∑ᶠ c : V ⧸ M, f (e c).out = ∑ᶠ c : V ⧸ M, f c.out := finsum_comp_equiv (f := fun c : V ⧸ M => f c.out) e
  simp only [he] at h3
  rw [← mul_finsum] at h3
  exact mul_right_cancel₀ h1 (by rw [h3, one_mul])

theorem eigen_eq_one : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E) (χ : K), (∀ t, f (T t + b) = χ * f t) → boxSum P N N f ≠ 0 → χ = 1 := by
  intro E _ _ K _ _ P hP ι _ _ f N hf T b χ hT hS
  have hq := NormalFormAtPrime.qOf_ne_zero P
  have h3 := rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP N N
  refine eigen_eq_one_of_reps f (boxSum_ne_zero_invariant_affineChange.lat P ι ((qOf P : E) ^ N)⁻¹)
    (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) N N) (fun v u hu => ?_) (fun s hs s' hs' h => ?_)
    (fun v hv => ?_) T.toAddEquiv b χ hT (right_ne_zero_of_mul hS)
  · have := hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul] at this
  · funext i
    exact h3.1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)
  · choose s hs hs' using fun i => h3.2 (v i) (hf.1 v hv i)
    exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩

end GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardFilterLeLogClassNumber
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

theorem prod_orderOf_le_card_of_indep {G ι : Type} [CommGroup G] [Fintype G] [Fintype ι] (x : ι → G)
    (hx : ∀ a : ι → ℤ, ∏ i, x i ^ a i = 1 → ∀ i, x i ^ a i = 1) : ∏ i, orderOf (x i) ≤ Fintype.card G := by
  classical
  have hinj : Function.Injective (fun a : (∀ i, Fin (orderOf (x i))) => ∏ i, x i ^ (a i : ℕ)) := by
    intro a a' h
    have h1 := hx (fun i => ((a i : ℕ) : ℤ) - ((a' i : ℕ) : ℤ)) (by
      simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      exact mul_inv_eq_one.2 h)
    funext i
    have h2 := h1 i
    rw [zpow_sub, zpow_natCast, zpow_natCast, mul_inv_eq_one] at h2
    exact Fin.ext (pow_injOn_Iio_orderOf (a i).2 (a' i).2 h2)
  simpa using Fintype.card_le_of_injective _ hinj

theorem card_filter_le_log_classNumber {E : Type} [Field E] [NumberField E] (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis E) :
    (Finset.univ.filter fun i => b.h i ≠ 1).card ≤ Nat.log 2 (classNumber E) := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  have h1 : ∏ i, b.h i ≤ classNumber E := prod_orderOf_le_card_of_indep _ b.indep
  refine le_trans ?_ h1
  rw [← Finset.prod_filter_ne_one]
  refine Finset.pow_card_le_prod _ _ _ fun i hi => ?_
  have h2 := (Finset.mem_filter.1 hi).2
  have h3 := b.h_pos i
  omega

theorem exists_kPsiField_generators (R : Ranks) (H : Host R) (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis H.E) (p q : ℕ) :
    ∃ S : Finset ℂ, S.card ≤ Nat.log 2 (classNumber H.E) ∧
      (∀ y ∈ S, ∃ n : ℕ, 0 < n ∧ n ∣ classNumber H.E ∧ y ^ n ∈ imField H.φ₀) ∧
      kPsiField H b p q = imField H.φ₀ ⊔ cycField (classNumber H.E) ⊔ IntermediateField.adjoin ℚ (S : Set ℂ) := by
  classical
  choose ψ hψ using fun i : Fin b.k =>
    IsAlgClosed.exists_pow_nat_eq (H.φ₀ (typeNorm H p q (b.γ i : H.E))) (b.h_pos i)
  refine ⟨(Finset.univ.filter fun i => b.h i ≠ 1).image ψ,
    Finset.card_image_le.trans (card_filter_le_log_classNumber b), fun y hy => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨b.h i, b.h_pos i, orderOf_dvd_card, _, (hψ i).symm⟩
  · rw [kPsiField_eq H b p q ψ hψ]
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      by_cases h : b.h i = 1
      · have h1 : ψ i ∈ imField H.φ₀ := ⟨_, by have := hψ i; rw [h, pow_one] at this; exact this.symm⟩
        exact (le_sup_left.trans le_sup_left : imField H.φ₀ ≤ _) h1
      · exact (le_sup_right : IntermediateField.adjoin ℚ _ ≤ _) (IntermediateField.subset_adjoin ℚ _
          (Finset.mem_coe.2 (Finset.mem_image_of_mem ψ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))))
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact ⟨i, rfl⟩

end GlobalTheory.Mem.Fld
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeNormGeneratorOfKummerFieldLe
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KPsiGen

open GlobalTheory.Mem.FieldsEx GlobalTheory.Mem.BaseExt GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis

variable {E : Type} [Field E] [NumberField E]

theorem typeNorm_of_root [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (𝔞 : Ideal (𝓞 E)) {h : ℕ} (hpos : 0 < h) (γ : 𝓞 E) (h0 : γ ≠ 0)
    (hγ : 𝔞 ^ h = Ideal.span {γ}) (β : K) (hb : (β : ℂ) ^ h = ∏ τ : E →+* ℂ, τ (γ : E) ^ r τ) : β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  classical
  have : NumberField K := NumberField.mk
  have hβ : β ^ h = ∏ τ : E →+* ℂ, τ.codRestrict K (hK τ) (γ : E) ^ r τ := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb]
    rfl
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow hpos.ne'] at hβ
    refine Finset.prod_ne_zero_iff.2 (fun τ _ => pow_ne_zero _ ?_) hβ.symm
    rw [map_ne_zero]; exact_mod_cast h0
  refine ⟨hβ0, ?_, fun σ => ?_⟩
  · simp only [fun τ => span_eq_extend K τ (hK τ)]
    refine (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ hpos hβ0
      (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_).symm
    rw [hβ, ← span_singleton_prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hγ, extendIdealHom_span]
  · have h1 := norm_typeNorm_sq_eq E r n hr K hK (γ : E) σ
    have h2 : ‖σ (β ^ h)‖ ^ 2 = (Ideal.absNorm (Ideal.span {γ}) : ℝ) ^ n := by
      rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, hβ]
      rw [← Algebra.coe_norm_int, Rat.cast_intCast] at h1
      exact h1
    rw [← hγ, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at h2
    exact (pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 h2

theorem exists_gen_basis (b : ClassBasis E) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ (γ : 𝓞 E) (α : Eˣ) (a : Fin b.k → ℤ) (k : Fin b.k → ℕ), γ ≠ 0 ∧ (∀ i, classNumber E = b.h i * k i) ∧
      𝔞 ^ classNumber E = Ideal.span {γ} ∧
      (γ : E) = ((α ^ classNumber E * ∏ i, (b.γ i ^ k i) ^ a i : Eˣ) : E) := by
  let 𝔠 : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  obtain ⟨a, ha⟩ := b.span (ClassGroup.mk E (FractionalIdeal.mk0 E 𝔠))
  have hk : ∀ i, ∃ k, classNumber E = b.h i * k := fun i => (orderOf_dvd_card : b.h i ∣ classNumber E)
  choose k hk using hk
  have h1 : ClassGroup.mk E (FractionalIdeal.mk0 E 𝔠 * (∏ i, b.c i ^ a i)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_prod, ha]
    simp only [map_zpow, mul_inv_cancel]
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hx
    exact Units.ne_zero _ hx
  have h2 : FractionalIdeal.mk0 E 𝔠 = toPrincipalIdeal (𝓞 E) E (Units.mk0 x hx0) * ∏ i, b.c i ^ a i := by
    rw [← mul_inv_eq_iff_eq_mul]
    exact Units.ext (by rw [hx, coe_toPrincipalIdeal]; rfl)
  set y : Eˣ := Units.mk0 x hx0 ^ classNumber E * ∏ i, (b.γ i ^ k i) ^ a i with hy
  have h3 : FractionalIdeal.mk0 E 𝔠 ^ classNumber E = toPrincipalIdeal (𝓞 E) E y := by
    rw [h2, hy, mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, map_pow, ← b.pow_eq i, ← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm, hk i]
    rfl
  have h4 : ((𝔞 ^ classNumber E : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (y : E) := by
    rw [← coe_toPrincipalIdeal, ← h3, FractionalIdeal.coeIdeal_pow, Units.val_pow_eq_pow_val]
    rfl
  have h5 : (y : E) ∈ ((𝔞 ^ classNumber E : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [h4]; exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨γ, -, hγ⟩ := (FractionalIdeal.mem_coeIdeal _).1 h5
  refine ⟨γ, Units.mk0 x hx0, a, k, ?_, hk, ?_, hγ⟩
  · rintro rfl
    exact y.ne_zero (by rw [← hγ, map_zero])
  · apply FractionalIdeal.coeIdeal_injective (K := E)
    simp only
    rw [h4, FractionalIdeal.coeIdeal_span_singleton, hγ]

theorem typeNorm_of_basis [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (b : ClassBasis E)
    (hb : ∀ i (z : ℂ), z ^ b.h i = ∏ τ : E →+* ℂ, τ (b.γ i : E) ^ r τ → z ∈ K)
    (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : ∃ β : K, β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  obtain ⟨γ, α, a, k, h0, hk, hγ, hy⟩ := exists_gen_basis b 𝔞 h𝔞
  let Ψ : Eˣ →* ℂ :=
    { toFun := fun x => ∏ τ : E →+* ℂ, τ (x : E) ^ r τ
      map_one' := by simp
      map_mul' := fun x y => by simp only [Units.val_mul, map_mul, mul_pow, Finset.prod_mul_distrib] }
  choose ψ hψ using fun i => IsAlgClosed.exists_pow_nat_eq (Ψ (b.γ i)) (b.h_pos i)
  have hm : Ψ α * ∏ i, ψ i ^ a i ∈ K :=
    mul_mem (prod_mem fun τ _ => pow_mem (hK τ _) _) (prod_mem fun i _ => zpow_mem (hb i _ (hψ i)) _)
  refine ⟨⟨_, hm⟩, typeNorm_of_root r n hr K hK 𝔞 (classNumber_pos E) γ h0 hγ _ ?_⟩
  rw [hy]
  change (Ψ α * ∏ i, ψ i ^ a i) ^ _ = Ψ _
  rw [mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, map_pow, ← hψ i, ← pow_mul, ← hk i, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm]

theorem typeNorm_gen_of_kPsi_le : ∀ (P : Pre) (δ : FieldDat P) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (j : ℕ), δ.KPsi j ≤ F → ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧ Submodule.span (𝓞 F) {β} = ∏ g : Tau P.R, (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (a : P.host.E))} ^ (P.R.sigW j).1 * Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (P.host.conj (a : P.host.E)))} ^ (P.R.sigW j).2) ∧ ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2) := by
  intro P δ F _ j hF 𝔞 h𝔞
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  have hgal : IsGalois ℚ P.host.E := P.host.hostE_isGalois
  simp only [FieldDat.KPsi, kPsiField, sup_le_iff, imField_le_iff, IntermediateField.adjoin_le_iff] at hF
  obtain ⟨⟨hE, -⟩, hψ⟩ := hF
  have hK : ∀ (τ : P.host.E →+* ℂ) x, τ x ∈ F := fun τ x => by
    obtain ⟨σ, hσ⟩ := exists_aut P.host.φ₀ τ
    rw [hσ]; exact hE _
  obtain ⟨β, hβ, hsp, hn⟩ := typeNorm_of_basis (typeExp P.host (P.R.sigW j).1 (P.R.sigW j).2) _
    (typeExp_add P.host _ _) F hK δ.basis (fun i z hz => hψ ⟨i, by
      rw [hz, prod_typeExp, typeNorm, map_prod]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [map_mul, map_pow, map_pow, conjugate_emb_apply]
      rfl⟩) 𝔞 h𝔞
  refine ⟨β, hβ, ?_, hn⟩
  rw [hsp, prod_typeExp]
  refine Finset.prod_congr rfl fun g _ => ?_
  simp only [conjugate_emb_apply]
  rfl

end GlobalTheory.Mem.KPsiGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetSpanConjMulIntegralOfIntegralPairing
section
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory

theorem detSpan_conj_mul_mem_range (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (M M' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) :
    ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M',
      IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  have hc : ∀ a : 𝓞 E, IsCMField.complexConj E (a : E) ∈ (algebraMap (𝓞 E) E).range := fun a =>
    ⟨IsCMField.ringOfIntegersComplexConj E a, IsCMField.coe_ringOfIntegersComplexConj E a⟩
  intro x hx y hy
  unfold GlobalTheory.BetaEx.detSpan at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M x).1 hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M' y).1 hy
      choose A hA using fun i k => h (v i) (hv i) (w k) (hw k)
      refine ⟨(Matrix.of A).det, ?_⟩
      have e1 : IsCMField.complexConj E v.det
          = ((IsCMField.complexConj E : E →+* E).mapMatrix v).det := by
        rw [← RingHom.map_det]; rfl
      rw [RingHom.map_det, e1, ← Matrix.det_transpose w, ← Matrix.det_mul]
      congr 1
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
        Matrix.transpose_apply, hA]
      rfl
    | zero => simpa using Subring.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Subring.add_mem _ ha hb
    | smul a b _ hb =>
      rw [Algebra.smul_def, mul_left_comm]
      exact Subring.mul_mem _ ⟨a, rfl⟩ hb
  | zero => simpa using Subring.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _), add_mul]; exact Subring.add_mem _ ha hb
  | smul a b _ hb =>
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact Subring.mul_mem _ (hc a) hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormModuloUnipotentSemidirect
section
namespace GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect

theorem latticeNormalForm : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm :=
  GlobalTheory.Proof.LatticeNormalFormUnipotent.latticeNormalForm

end GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect
end

