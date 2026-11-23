module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.GaloisClause
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfIsAlgebraic
section
noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

theorem exists_eq_of_isAlgebraic (ι : Qb →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) : ∃ x, ι x = z := by
  let := ι.toAlgebra
  have hi : IsIntegral Qb z := (hz.tower_top Qb).isIntegral
  exact minpoly.mem_range_of_degree_eq_one Qb z
    (IsAlgClosed.degree_eq_one_of_irreducible Qb (minpoly.irreducible hi))

def qbEquiv (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] : qb ι M ≃+* M :=
  RingEquiv.ofBijective ((ι.comp (qb ι M).val.toRingHom).codRestrict M fun x => x.2) ⟨RingHom.injective _, fun z => by
    obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι
      (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z))
    exact ⟨⟨x, mem_qb.2 (hx ▸ z.2)⟩, Subtype.ext hx⟩⟩

theorem numberField_qb (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] : NumberField (qb ι M) :=
  NumberField.of_ringEquiv M _ (qbEquiv ι M).symm

variable {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb)

@[instance_reducible] def algThrough (L : Fld) (h : j.fieldRange ≤ L) : Algebra E L :=
  (j.toRingHom.codRestrict L fun x => h ⟨x, rfl⟩).toAlgebra

theorem finrank_div (L : Type) [Field L] [NumberField L] [Algebra E L] :
    Module.finrank ℚ L / Module.finrank ℚ E = Module.finrank E L := by
  rw [← Module.finrank_mul_finrank ℚ E L, Nat.mul_div_cancel_left _ Module.finrank_pos]

theorem isRayField_qb (ι : Qb →+* ℂ) {𝔮 : Ideal (𝓞 E)} {M : IntermediateField ℚ ℂ}
    (hM : IsRayFieldIn (ι.comp j.toRingHom) 𝔮 M) :
    ∃ (_ : NumberField (qb ι M)) (h : j.fieldRange ≤ qb ι M), letI := algThrough j _ h; IsRayField E (qb ι M) 𝔮 := by
  obtain ⟨h, hN, hR⟩ := hM
  have hle : j.fieldRange ≤ qb ι M := by
    rintro _ ⟨x, rfl⟩
    exact h x
  refine ⟨numberField_qb ι M, hle, ?_⟩
  let := algOf _ M h
  let := algThrough j _ hle
  have := numberField_qb ι M
  exact hR.of_algEquiv (AlgEquiv.ofRingEquiv (f := qbEquiv ι M) fun x => rfl).symm

theorem le_of_algHom {L N : Fld} (hL : j.fieldRange ≤ L) (hN : j.fieldRange ≤ N)
    (hn : letI := algThrough j L hL; Normal E L)
    (ψ : letI := algThrough j L hL; letI := algThrough j N hN; L →ₐ[E] N) : L ≤ N := by
  let := algThrough j L hL
  let := algThrough j N hN
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E N Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ : L →ₐ[E] Qb := (IsScalarTower.toAlgHom E N Qb).comp ψ
  intro x hx
  obtain ⟨y, hy⟩ := (φ.restrictNormal' L).surjective ⟨x, hx⟩
  have h1 : algebraMap L Qb (φ.restrictNormal' L y) = φ y := φ.restrictNormal_commutes L y
  rw [hy] at h1
  have h2 : x = (ψ y : Qb) := h1
  exact h2 ▸ (ψ y).2

theorem isAbelianGalois_iff (L : Fld) (h : j.fieldRange ≤ L) :
    (letI := algThrough j L h; IsAbelianGalois E L) ↔
      ∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ L, s (t x) = t (s x) := by
  let := algThrough j L h
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ E Qb := IsScalarTower.of_algebraMap_eq fun q => (j.commutes q).symm
  have : IsAlgClosure ℚ Qb := AlgebraicClosure.instIsAlgClosure ℚ
  have : IsGalois ℚ Qb := IsAlgClosure.isGalois ℚ Qb
  have : IsGalois E Qb := IsGalois.tower_top_of_isGalois ℚ E Qb
  have hmem : ∀ s : Qb ≃ₐ[E] Qb, s.restrictScalars ℚ ∈ GalOf j.fieldRange := fun s => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, rfl⟩
    exact s.commutes x
  constructor
  · intro hab s hs t ht x hx
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ht
    let s' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩
    let t' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := t.toRingEquiv) fun y => ht _ ⟨y, rfl⟩
    have hc : AlgEquiv.restrictNormalHom L (s' * t') = AlgEquiv.restrictNormalHom L (t' * s') := by
      rw [map_mul, map_mul, IsMulCommutative.is_comm.comm]
    have h1 := AlgEquiv.restrictNormal_commutes (s' * t') L ⟨x, hx⟩
    have h2 := AlgEquiv.restrictNormal_commutes (t' * s') L ⟨x, hx⟩
    have h3 : (s' * t').restrictNormal L = (t' * s').restrictNormal L := hc
    rw [h3, h2] at h1
    exact h1.symm
  · intro H
    have hst : ∀ s : Qb ≃ₐ[E] Qb, ∀ x ∈ L, s x ∈ L := fun s x hx => by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro t ht
      have h1 := H t (IntermediateField.fixingSubgroup_antitone h ht) _ (hmem s) x hx
      rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 ht x hx] at h1
      exact h1
    let L' : IntermediateField E Qb := (IsScalarTower.toAlgHom E L Qb).fieldRange
    have hn' : Normal E L' := IntermediateField.normal_iff_forall_map_le'.2 fun s => by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨⟨_, hst s x x.2⟩, rfl⟩
    let e : L ≃ₐ[E] L' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom E L Qb)
    have hn : Normal E L := Normal.of_algEquiv e.symm
    have : IsGalois E L := {}
    refine { is_comm := ⟨fun a b => ?_⟩ }
    obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb a
    obtain ⟨t, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb b
    rw [← map_mul, ← map_mul]
    refine AlgEquiv.ext fun x => (algebraMap L Qb).injective ?_
    exact (AlgEquiv.restrictNormal_commutes (s * t) L x).trans
      ((H _ (hmem s) _ (hmem t) x x.2).trans (AlgEquiv.restrictNormal_commutes (t * s) L x).symm)

theorem map_mem_of_normal (L : Fld) (h : j.fieldRange ≤ L) (hn : letI := algThrough j L h; Normal E L) :
    ∀ s ∈ GalOf j.fieldRange, ∀ x ∈ L, s x ∈ L := by
  let := algThrough j L h
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro s hs x hx
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs
  let s' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩
  have h1 : ((s'.restrictNormal L ⟨x, hx⟩ : L) : Qb) = s x := AlgEquiv.restrictNormal_commutes s' L ⟨x, hx⟩
  exact h1 ▸ (s'.restrictNormal L ⟨x, hx⟩).2


omit j in
theorem hilbert_qb : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ), IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ (_ : NumberField (qb ι M)) (h : j.fieldRange ≤ qb ι M),
      (letI := algThrough j _ h; IsAbelianGalois E (qb ι M)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L] (hL : j.fieldRange ≤ L), (letI := algThrough j L hL; IsAbelianGalois E L) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hR⟩ := isRayField_qb j ι hM
  let := algThrough j _ h
  have := hR.1
  refine ⟨hN, h, hR.1, ?_, fun L _ hL hab hd => ?_⟩
  · rw [finrank_div]
    exact (GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E _).1 fun 𝔭 =>
      hR.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd))
  · let := algThrough j L hL
    rw [finrank_div] at hd
    obtain ⟨ψ⟩ := GlobalTheory.UnramInRay.nonempty_algHom_rayField H E L (qb ι M) ⊤ top_ne_bot hR
      ((GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E L).2 hd)
    exact le_of_algHom j hL h inferInstance ψ


omit j in
theorem hilbert_qb_aut : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ), IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M), j.fieldRange ≤ qb ι M ∧
      (∀ s ∈ GalOf j.fieldRange, ∀ x ∈ qb ι M, s x ∈ qb ι M) ∧
      (∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ qb ι M, s (t x) = t (s x)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L], j.fieldRange ≤ L →
        (∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ L, s (t x) = t (s x)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hab, hd, hmax⟩ := hilbert_qb H E j ι M hM
  refine ⟨hN, h, map_mem_of_normal j _ h ?_, (isAbelianGalois_iff j _ h).1 hab, hd,
    fun L _ hL hc => hmax L hL ((isAbelianGalois_iff j L hL).2 hc)⟩
  let := algThrough j _ h
  infer_instance

end GlobalTheory.HilbertInClosure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CuspTwist

open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES PI.GreenLabelMapW IntermediateField

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem algebraMap_det_eq_pow {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K)
    (hγ : Irreducible (γ : Matrix ι ι K).charpoly) {z : AlgebraicClosure K}
    (hz : aeval z (γ : Matrix ι ι K).charpoly = 0) :
    algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix ι ι K)) =
      z ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i := by
  have hint : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hmin : (γ : Matrix ι ι K).charpoly = minpoly K z :=
    minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)
  have hdeg : (minpoly K z).natDegree = Fintype.card ι := by
    rw [← hmin, Matrix.charpoly_natDegree_eq_dim]
  let pb := IntermediateField.adjoin.powerBasis hint
  have hnorm : Algebra.norm K pb.gen = Matrix.det (γ : Matrix ι ι K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, Matrix.det_eq_sign_charpoly_coeff, hmin]
    have h1 : pb.dim = Fintype.card ι := by
      rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
    have h2 : pb.gen = IntermediateField.AdjoinSimple.gen K z := IntermediateField.adjoin.powerBasis_gen hint
    rw [h1, h2, IntermediateField.minpoly_gen]
  haveI : FiniteDimensional K K⟮z⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K⟮z⟯ := Module.finite_of_finite K
  have hfr : Module.finrank K K⟮z⟯ = Fintype.card ι := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have h3 := FiniteField.algebraMap_norm_eq_pow_sum (K := K) (L := K⟮z⟯) (x := pb.gen)
  rw [hnorm, hfr, Nat.card_eq_fintype_card] at h3
  have h5 : ((pb.gen ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i : K⟮z⟯) :
      AlgebraicClosure K) = z ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i := by
    rw [IntermediateField.coe_pow, IntermediateField.adjoin.powerBasis_gen hint,
      IntermediateField.AdjoinSimple.coe_gen]
  rw [← h5, ← h3]
  rfl

theorem gen_one_pow_eq_det (Cv : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : 1 ≤ Fintype.card ι) (γ : GL ι K) (hγ : Irreducible (γ : Matrix ι ι K).charpoly)
    {z : AlgebraicClosure K} (hz : aeval z (γ : Matrix ι ι K).charpoly = 0) {m : ℕ}
    (hm : Cv.gen (Fintype.card ι) ^ m = z) :
    Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix ι ι K)) := by
  have hn := Cv.gen_norm 1 (Fintype.card ι) le_rfl hι
  rw [one_mul, pow_one] at hn
  rw [algebraMap_det_eq_pow γ hγ hz, ← hn, ← hm, ← pow_mul, ← pow_mul,
    Nat.geomSum_eq Fintype.one_lt_card, mul_comm]

theorem twist_clause (Cv : LabelConv K) (hC : CuspParam K Cv) (d : ℕ)
    (τ τ' : FDRep ℂ (GL (Fin d) K)) (x : K) (hd : 1 ≤ d) (hx : x ≠ 0) (hs : Simple τ)
    (hc : IsCuspidal K τ) (hs' : Simple τ') (hc' : IsCuspidal K τ')
    (htr : ∀ (γ : GL (Fin d) K) (m : ℕ),
      Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin d) (Fin d) K)) →
      LinearMap.trace ℂ τ' (τ'.ρ γ) =
        Cv.ι (algebraMap K (AlgebraicClosure K) x) ^ m * LinearMap.trace ℂ τ (τ.ρ γ)) :
    rootsBar K (greenLab Cv d τ') =
      (rootsBar K (greenLab Cv d τ)).map (· * algebraMap K (AlgebraicClosure K) x) := by
  set xb := algebraMap K (AlgebraicClosure K) x with hxb
  have hxb0 : xb ≠ 0 := by
    rw [hxb]; exact (map_ne_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).2 hx
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := greenLab_spec Cv hC hd hs hc
  have hdeg' : (greenLab Cv d τ).natDegree = d := by rw [hdeg, Fintype.card_fin]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (greenLab Cv d τ)
    (by rw [degree_eq_natDegree hm.ne_zero, hdeg']; exact_mod_cast (show d ≠ 0 by omega))
  have hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (y : AlgebraicClosure K),
      σ y * xb = σ (y * xb) := fun σ y => by rw [map_mul, hxb, AlgEquiv.commutes]
  have hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ (greenLab Cv d τ) = 0 →
      aeval r₂ (greenLab Cv d τ) = 0 → r₁ * xb = r₂ * xb → r₁ = r₂ :=
    fun _ _ _ _ h => mul_right_cancel₀ hxb0 h
  have hint : IsIntegral K (w * xb) := Algebra.IsIntegral.isIntegral _
  have hxq : ∀ i : ℕ, xb ^ (Fintype.card K ^ i) = xb := fun i => by
    rw [hxb, ← map_pow, FiniteField.pow_card_pow]
  have hlab : HasCuspLabel Cv τ' (minpoly K (w * xb)) := by
    refine ⟨minpoly.monic hint, minpoly.irreducible hint, ?_, ?_, ?_⟩
    · intro h
      have h0 := minpoly.aeval K (w * xb)
      rw [h, aeval_X] at h0
      exact mul_ne_zero (root_ne_zero hm hi hX hw) hxb0 h0
    · rw [natDegree_minpoly_eq hm hi hw (fun y => y * xb) hf hinj, hdeg]
    · intro y hy γ hγ z hz m hm'
      obtain ⟨r, hr, rfl⟩ := (conj_roots hm hi hw (fun y => y * xb) hf y).1 hy
      have hι : 1 ≤ Fintype.card (Fin d) := by rw [Fintype.card_fin]; exact hd
      rw [htr γ m (gen_one_pow_eq_det Cv hι γ hγ hz hm'), hval r hr γ hγ z hz m hm',
        mul_left_comm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : Cv.ι xb ^ (m * Fintype.card K ^ i) = Cv.ι xb ^ m := by
        rw [mul_comm, pow_mul, ← map_pow, hxq i]
      rw [map_mul, mul_pow, e, mul_comm]
  rw [greenLab_eq Cv hC hd hs' hc' hlab]
  exact aroots_eq_map hm hi hw (fun y => y * xb) hf hinj

theorem exists_labelMap_twist_cuspLabel :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K),
      Formalism.IrreducibleCountingLemmas.TYPES.CuspParam K C → ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C,
        Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
          ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → CategoryTheory.Simple τ →
            Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ (O.lab d τ) := by
  intro K _ _ _ Cv hC
  let O : LabelMap K Cv :=
    { lab := greenLab Cv
      lab_iso := greenLab_iso Cv
      lab_spec := fun d τ hd hs hc => by
        obtain ⟨h1, h2, h3, h4, -⟩ := greenLab_spec Cv hC hd hs hc
        exact ⟨h1, h2, h3, by rw [h4, Fintype.card_fin]⟩
      lab_inj := fun d τ τ' hd hs hc hs' hc' h =>
        (hC d hd).2.2 τ τ' (greenLab Cv d τ) hs hc hs' hc' (greenLab_spec Cv hC hd hs hc)
          (by rw [h]; exact greenLab_spec Cv hC hd hs' hc')
      lab_one := fun τ x hs hx htr => greenLab_one Cv hC τ x hs hx htr }
  refine ⟨O, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro d α a hα τ τ' hd hs hc hs' hc' htr
    exact galois_clause Cv hC d α a hα τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' hd hs hc hs' hc' htr
    exact dual_clause Cv hC d τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' x hd hx hs hc hs' hc' htr
    exact twist_clause Cv hC d τ τ' x hd hx hs hc hs' hc' htr
  · intro d τ hd hs hc
    exact greenLab_spec Cv hC hd hs hc

end GlobalTheory.CuspTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitEmb
open GlobalTheory.SplitLift

section General
variable {n : ℕ} {K : Type*} (A : Type*) [CommRing K] [CommRing A]

def triMat (M : GL (Fin n) K) : Matrix (Fin n) (Fin n) (K × K × A) :=
  fun i j => ((M : Matrix (Fin n) (Fin n) K) i j, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j i,
    (1 : Matrix (Fin n) (Fin n) A) i j)

theorem triMat_one : triMat A (1 : GL (Fin n) K) = 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [triMat, inv_one, Units.val_one, Matrix.one_apply, eq_comm (a := j)]
  split_ifs <;> rfl

theorem triMat_mul (M N : GL (Fin n) K) : triMat A (M * N) = triMat A M * triMat A N := by
  symm
  apply matrix_prod_ext
  · exact Matrix.map_mul (L := triMat A M) (M := triMat A N) (f := RingHom.fst K (K × A))
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.fst K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    change ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose *
      ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose =
      (((M * N)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.snd K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    exact Matrix.mul_one (1 : Matrix (Fin n) (Fin n) A)

end General

theorem exists_hom_trivOutside_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L),
    ∃ e : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) →* GAf L n,
      (∀ g, TrivOutside {s.v} (e g)) ∧ ∀ g, s.loc n (e g) = g := by
  intro L _ _ _ n s
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : IsCMField.complexConj L (δ * δ) = δ * δ := by rw [map_mul, hδ]; ring
  let d : maximalRealSubfield L := ⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩
  have hd : δ * δ = algebraMap (maximalRealSubfield L) L d := rfl
  have hr : s.i δ ≠ 0 := (map_ne_zero _).2 hδ0
  let X : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) → Matrix (Fin n) (Fin n) (AL L) :=
    fun M => (triMat (AL L) M).map (θ s δ d hd hr)
  have hX1 : X 1 = 1 := by
    show (triMat (AL L) 1).map (θ s δ d hd hr) = 1
    rw [triMat_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXm : ∀ M N, X (M * N) = X M * X N := fun M N => by
    show (triMat (AL L) (M * N)).map (θ s δ d hd hr) = _
    rw [triMat_mul, Matrix.map_mul]
  have hconj : ∀ M, conjT (conjAL L) (X M) = X M⁻¹ := fun M => by
    refine Matrix.ext fun i j => ?_
    simp only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]
    rw [conj_θ s δ d hd hr hδ]
    congr 1
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [triMat, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have hX : ∀ M, X M * conjT (conjAL L) (X M) = 1 := fun M => by
    rw [hconj, ← hXm, mul_inv_cancel, hX1]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := fun M => ⟨⟨X M, conjT (conjAL L) (X M), hX M, mul_eq_one_comm.mp (hX M)⟩, hX M⟩
      map_one' := Subtype.ext (Units.ext hX1)
      map_mul' := fun M N => Subtype.ext (Units.ext (hXm M N)) }
  refine ⟨e, fun M w hw => ?_, fun M => ?_⟩
  · have hw' : w ≠ s.v := hw
    refine Matrix.ext fun i j => ?_
    change compAt L w (θ s δ d hd hr (triMat (AL L) M i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [compAt_θ s δ d hd hr _ hw']
    simp only [triMat, Matrix.one_apply]
    split_ifs <;> simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change s.proj (θ s δ d hd hr (triMat (AL L) M i j)) = _
    rw [proj_θ]
    rfl

end GlobalTheory.SplitEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.SphCyclic

variable {L : Type} [Field L] [NumberField L] {P : HeightOneSpectrum (𝓞 L)}

theorem nrm_eq {nrm : AbsoluteValue (P.adicCompletion L) ℝ} (h : IsNrm P nrm) (x : (P.adicCompletion L)ˣ) :
    nrm x = (qP P : ℝ) ^ (WithZero.log (Valued.v (x : P.adicCompletion L))) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective L P (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  set m := WithZero.log (Valued.v (x : P.adicCompletion L)) with hm
  have hx : Valued.v (x : P.adicCompletion L) = WithZero.exp m := (WithZero.exp_log (by simp)).symm
  have h1 : nrm π = (qP P : ℝ)⁻¹ := (h (Units.mk0 π hπ0)).2 hπ
  have h2 := (h (x * (Units.mk0 π hπ0) ^ m)).1 (by
    show Valued.v ((x * (Units.mk0 π hπ0) ^ m : (P.adicCompletion L)ˣ) : P.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0,
      hπ, hx, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp)
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, h1, _root_.inv_zpow] at h2
  exact eq_of_div_eq_one h2

theorem exists_isUnrM : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (nrm : AbsoluteValue (P.adicCompletion L) ℝ), IsNrm P nrm → ∀ (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsNu P (ν i)) → ∀ r t j : ℕ, 1 ≤ t → ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (ρ : GL (Fin r) (P.adicCompletion L) × GL (Fin (j * t)) (P.adicCompletion L) →* (V ≃ₗᵢ[ℂ] V)), IsUnrM (OP P) nrm r (j * t) (satC nrm ν t (j * t)) ρ := by
  intro L _ _ P nrm hn ν hν r t j _
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hK : GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (j * t)) = GLint (OP P) (j * t) := by
    ext g
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
    exact Iff.rfl
  obtain ⟨V, _, _, ρ, h1, h2, v, h3, h4, φ, κ, h5, h6, h7, h8, h9, h10⟩ :=
    @exists_rep_eqBlocks (P.adicCompletion L) _ _ _ _ j t (instMeasGL _) (instBorelGL _) (fun a => ν (a + 1))
      (fun a => (hν _).unitary) (fun a x hx => (hν _).unr x (he.eq_one_iff_eq_one.1 hx))
      (GL (Fin r) (P.adicCompletion L)) _ _
  rw [hK] at h4 h6 h9 h10
  refine ⟨V, inferInstance, inferInstance, ρ, h1, h2, v, h3, fun k₁ _ => h4 k₁, φ, κ, fun b hb k hk => ?_,
    h8.toIsMulLeftInvariant, h9, h10⟩
  have hd : ∀ x, b.val x x ≠ 0 := by
    have := b.det_ne_zero
    rw [det_of_upperTriangular hb] at this
    exact fun x => Finset.prod_ne_zero_iff.1 this x (Finset.mem_univ _)
  have h11 := h5 b (fun x => Units.mk0 _ (hd x)) (fun x y h => hb h) (fun _ => rfl) 1
  rw [mul_one, h7, mul_one] at h11
  rw [h6 b k hk, h11]
  refine Finset.prod_congr rfl fun x _ => ?_
  have h12 : GlobalTheory.SplitWeil.nabs (P.adicCompletion L) (Units.mk0 _ (hd x)) = nrm (b.val x x) :=
    (GlobalTheory.LGrp.BorelCompletion.nabs_completion P _).trans (nrm_eq hn (Units.mk0 _ (hd x))).symm
  rw [h12, satC, chi0, dite_eq_right (hd x), mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (nrm.pos (hd x))]
  congr 3
  have : ((x : ℕ) : ℝ) = (((x : ℕ) % t : ℕ) : ℝ) + (((x : ℕ) / t : ℕ) : ℝ) * t := by
    exact_mod_cast (Nat.mod_add_div' (x : ℕ) t).symm
  linarith

end GlobalTheory.SphCyclic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemPvSet
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.PlaceOverPair

theorem exists_mem_pvSet {R : Ranks} (H : Formalism.BasicNotions.Host R) {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 H.K))
    (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal) (v : HeightOneSpectrum (𝓞 H.F)) (hv : OverPF H p v) : ∃ w, w ∈ PvSet H 𝔭 v := by
  obtain ⟨w, h1, h2⟩ := exists_over_both H hp 𝔭 h𝔭 v hv
  refine ⟨w, ?_, h2⟩
  rw [aboveF, Set.Finite.mem_toFinset]
  exact h1

end GlobalTheory.PlaceOverPair
end

