module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0135
public import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPDelStdOfIsBasisAt
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.WeylLocal

variable {K : Type} [Field K] [NumberField K]

abbrev locRing (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors

theorem mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ w.asIdeal.primeCompl),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

theorem isLocalRing_locRing (w : HeightOneSpectrum (𝓞 K)) : IsLocalRing (locRing w) :=
  IsLocalization.AtPrime.isLocalRing (locRing w) w.asIdeal

theorem ne_zero_of_mem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∈ w.asIdeal.primeCompl) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have h0 : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])
  exact hs (by rw [h0]; exact w.asIdeal.zero_mem)

theorem smul_mem_locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {a : K} (ha : a ∈ locRing w) {y : Z}
    (hy : y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) : a • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
  obtain ⟨s, hs, hsy⟩ := hy
  obtain ⟨r, t, ht, hat⟩ := (mem_locRing w a).mp ha
  refine ⟨t * s, mul_mem ht hs, ?_⟩
  have ht0 := ne_zero_of_mem w ht
  have he : (t * s) • (a • y) = r • (s • y) := by
    rw [hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
      ← algebraMap_smul K s, smul_smul, smul_smul]
    congr 1
    rw [map_mul]
    field_simp
  rw [he]
  exact M.smul_mem r hsy

theorem le_locP {Z : Type} [AddCommGroup Z] [Module (𝓞 K) Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {y : Z} (hy : y ∈ M) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M :=
  ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hy⟩

theorem coord_of_mem_colLat {n : ℕ} (B : GL (Fin n) K) {x : Fin n → K} (hx : x ∈ colLat B) (i : Fin n) :
    (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have h : (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        fun a => (B : Matrix (Fin n) (Fin n) K) a j) i =
        (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) i j := rfl
    rw [h, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ hy

theorem coord_of_mem_locP {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K) {x : Fin n → K}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B)) (i : Fin n) :
    (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) i ∈ locRing w := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨a, ha⟩ := coord_of_mem_colLat B hsx i
  rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def] at ha
  refine (mem_locRing w _).mpr ⟨a, s, hs, ?_⟩
  have hs0 := ne_zero_of_mem w hs
  rw [ha]
  field_simp

theorem entries_mem {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (h : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B')) (i j : Fin n) :
    ((B⁻¹ * B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ locRing w := by
  have hx : (fun a => (B' : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B) := by
    rw [h]
    exact le_locP w _ (Submodule.subset_span ⟨j, rfl⟩)
  exact coord_of_mem_locP w B hx i

theorem exists_lift {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ g₀ : Matrix (Fin n) (Fin n) (locRing w), IsUnit g₀.det ∧
      g₀.map (algebraMap (locRing w) K) = (g : Matrix (Fin n) (Fin n) K) := by
  have h1 := entries_mem w 1 g h
  have h2 := entries_mem w g 1 h.symm
  rw [inv_one, one_mul] at h1
  rw [mul_one] at h2
  let g₀ : Matrix (Fin n) (Fin n) (locRing w) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let g₁ : Matrix (Fin n) (Fin n) (locRing w) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have e0 : g₀.map (algebraMap (locRing w) K) = (g : Matrix (Fin n) (Fin n) K) := rfl
  have e1 : g₁.map (algebraMap (locRing w) K) = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  refine ⟨g₀, ?_, e0⟩
  have hm : g₀ * g₁ = 1 := by
    apply Matrix.map_injective (f := algebraMap (locRing w) K) Subtype.val_injective
    simp only
    rw [Matrix.map_mul, e0, e1, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_right_inverse hm

theorem map_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (ν : Fin n → ℕ)
    {f : MvPolynomial (Fin n × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν) :
    map φ f ∈ Formalism.GradedWeylDivisibility.weyl S n n le_rfl ν := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem toK_apply {σ : Type} (f : MvPolynomial σ (𝓞 K)) : toK K σ f = map (algebraMap (𝓞 K) K) f := rfl

theorem map_weyl_mem_locP (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ν : Fin n → ℕ)
    {f : MvPolynomial (Fin n × Fin n) (locRing w)} (hf : f ∈ Formalism.GradedWeylDivisibility.weyl (locRing w) n n le_rfl ν) :
    map (algebraMap (locRing w) K) f ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K _)) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine le_locP w _ ⟨_, Submodule.subset_span ⟨v, rfl⟩, ?_⟩
    simp only
    rw [toK_apply, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map,
      ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact smul_mem_locP w _ a.2 hy

theorem sqAct_mem_locP (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (lam : DomWeight n) (g : GL (Fin n) K)
    (h : IsBasisAt w (colLat 1) g) {f : MvPolynomial (Fin n × Fin n) K}
    (hf : f ∈ (delSq (𝓞 K) n lam).map (toK K _)) :
    sqAct K n lam g f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n lam).map (toK K _)) := by
  obtain ⟨g₀, hu, e0⟩ := exists_lift w g h
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  haveI := isLocalRing_locRing w
  have h1 := map_mem_weyl (algebraMap (𝓞 K) (locRing w)) lam.natW hf₀
  have h2 := GlobalTheory.TestLat.weyl_rowAct_mem_of_isUnit_det (locRing w) n lam.natW (natW_antitone lam) g₀ᵀ (by rwa [Matrix.det_transpose]) _ h1
  have h3 := map_weyl_mem_locP w lam.natW h2
  rw [Formalism.GradedWeylDivisibility.ldtwist_map_rowAct, map_map, ← IsScalarTower.algebraMap_eq, Matrix.transpose_map, e0] at h3
  refine smul_mem_locP w _ ?_ h3
  have hd : Matrix.GeneralLinearGroup.det g = Units.map (algebraMap (locRing w) K).toMonoidHom hu.unit := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← e0, Units.coe_map, IsUnit.unit_spec]
    exact ((algebraMap (locRing w) K).map_det g₀).symm
  rw [detPow, hd, ← map_zpow, Units.coe_map]
  exact Subtype.property _

theorem ten_mem_locP (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] {n : ℕ}
    (M : ι → Submodule (𝓞 K) (MvPolynomial (Fin n × Fin n) K)) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (M τ)) :
    ten f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.GradedWeylDivisibility.tensorLat (𝓞 K) K M) := by
  choose s hs hsf using hf
  refine ⟨∏ τ, s τ, prod_mem fun τ _ => hs τ, Submodule.subset_span ⟨fun τ => s τ • f τ, hsf, ?_⟩⟩
  rw [ten, ← Finset.prod_smul]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact ((Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap.map_smul_of_tower (s τ) (f τ)).symm

theorem polyAction_mem_locP_delStd : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  intro K _ _ ι _ n lam w g hg F hF
  have key : ∀ P ∈ delStd K lam, actP lam g P ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      have h := actTen K ι n lam g f
      rw [ten] at h
      rw [h]
      exact ten_mem_locP w _ _ fun τ => sqAct_mem_locP w (lam τ) (g τ) (hg τ) (hf τ)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ hy
  obtain ⟨s, hs, hsF⟩ := hF
  obtain ⟨t, ht, h⟩ := key _ hsF
  rw [LinearMap.map_smul_of_tower] at h
  exact ⟨t * s, mul_mem ht hs, (mul_smul t s (actP lam g F)).symm ▸ h⟩

end GlobalTheory.TestLat.WeylLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.NabStab

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem int_of_mem_colLat_one {x : Fin n → K} (hx : x ∈ colLat (1 : GL (Fin n) K)) (a : Fin n) :
    ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x a := by
  unfold colLat at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨j, rfl⟩ := h
    by_cases h : a = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [Matrix.one_apply, h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]; rfl⟩
  | smul r x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨r * u, by rw [map_mul, hu, Pi.smul_apply, Algebra.smul_def]⟩

theorem exists_int (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix (Fin n) (Fin n) (𝓞 K),
      A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • (g : Matrix (Fin n) (Fin n) K) := by
  classical
  have h1 : ∀ j : Fin n, (fun a : Fin n => (g : Matrix (Fin n) (Fin n) K) a j) ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat (1 : GL (Fin n) K)) := by
    intro j
    unfold IsBasisAt at h
    rw [h]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  choose s hs hs' using h1
  have h2 : ∀ a j : Fin n, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K (∏ i, s i) * (g : Matrix (Fin n) (Fin n) K) a j := by
    intro a j
    obtain ⟨y, hy⟩ := int_of_mem_colLat_one (hs' j) a
    refine ⟨(∏ i ∈ Finset.univ.erase j, s i) * y, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, map_mul, hy, Pi.smul_apply, Algebra.smul_def,
      mul_assoc]
  choose A hA using h2
  refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, Matrix.of A, ?_⟩
  ext a j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hA]

theorem isBasisAt_inv (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    IsBasisAt w (colLat 1) g⁻¹ := by
  rw [← isBasisAt_gLat w g, ← colLat_mul, mul_one, mul_inv_cancel]
  exact h.symm

theorem det_int (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) := by
  obtain ⟨t, ht, A, hA⟩ := exists_int w g h
  refine ⟨t ^ n, Submonoid.pow_mem _ ht n, A.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_smul, map_pow]
  simp

theorem detPow_int (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g) (e : ℤ) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * detPow K n g e := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · obtain ⟨t, ht, y, hy⟩ := det_int w g h
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, map_pow, mul_pow, detPow, zpow_natCast, Units.val_pow_eq_pow_val]
  · obtain ⟨t, ht, y, hy⟩ := det_int w g⁻¹ (isBasisAt_inv w g h)
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, map_pow, mul_pow, detPow, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, map_inv]

theorem degree_of_weight {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem rowAct_smul {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f ν) :
    Formalism.GradedWeylDivisibility.rowAct R (c • g) f = c ^ (∑ j, ν j) • Formalism.GradedWeylDivisibility.rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_weight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.rowAct R g f) = Formalism.GradedWeylDivisibility.rowAct S (g.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp]
    simp [Formalism.GradedWeylDivisibility.rowAct]

theorem toK_apply {σ : Type} (f : MvPolynomial σ (𝓞 K)) : toK K σ f = map (algebraMap (𝓞 K) K) f := rfl

theorem sqAct_mem (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (h : IsBasisAt w (colLat 1) g)
    (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) K) (hf : f ∈ (nablaSq (𝓞 K) n lam).map (toK K _)) :
    ∃ s ∈ w.asIdeal.primeCompl,
      algebraMap (𝓞 K) K s • sqAct K n lam g f ∈ (nablaSq (𝓞 K) n lam).map (toK K _) := by
  obtain ⟨f, hf, rfl⟩ := hf
  obtain ⟨t, ht, A, hA⟩ := exists_int w g h
  obtain ⟨u, hu, y, hy⟩ := detPow_int w g h lam.detShift
  refine ⟨u * t ^ (∑ j, lam.natW j), Submonoid.mul_mem _ hu (Submonoid.pow_mem _ ht _),
    y • Formalism.GradedWeylDivisibility.rowAct (𝓞 K) Aᵀ f,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable (𝓞 K) n n _ _ f hf), ?_⟩
  have hK : map (algebraMap (𝓞 K) K) f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n lam.natW :=
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ f hf
  have hT : Aᵀ.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • (g : Matrix (Fin n) (Fin n) K)ᵀ := by
    rw [Matrix.transpose_map, hA, Matrix.transpose_smul]
  rw [map_smul, toK_apply, toK_apply, map_rowAct, hT, rowAct_smul _ _ _ hK.1, sqAct,
    ← IsScalarTower.algebraMap_smul K y, hy, smul_smul, smul_smul, map_mul, map_pow]
  congr 1
  ring

theorem polyAction_mem_locP_nabStd (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K) (h : ∀ τ, IsBasisAt w (colLat 1) (g τ)) :
    ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have key : ∀ F ∈ nabStd K lam, actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
    intro F hF
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      choose s hs hs' using fun τ => sqAct_mem w (g τ) (h τ) (lam τ) (f τ) (hf τ)
      refine ⟨∏ τ, s τ, Submonoid.prod_mem _ fun τ _ => hs τ, Submodule.subset_span ⟨_, hs', ?_⟩⟩
      have h1 := actTen K ι n lam g f
      unfold ten at h1
      rw [h1, ← IsScalarTower.algebraMap_smul K, map_prod]
      simp only [map_smul]
      exact (Finset.prod_smul _ _ _).symm
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ hx
  rintro F ⟨s, hs, hF⟩
  obtain ⟨t, ht, h2⟩ := key _ hF
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [LinearMap.map_smul_of_tower] at h2
  rw [mul_smul]
  exact h2

end GlobalTheory.NabStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockActMemRangeMapSubtype
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

section

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def nonnegRing_vw (w : HeightOneSpectrum (𝓞 K)) : Subring K where
  carrier := {a | 0 ≤ vw w a}
  zero_mem' := (ValuationRepresentative.vw_zero w).ge
  one_mem' := (ValuationRepresentative.vw_one w).ge
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    by_cases h0 : a = 0
    · rw [h0, zero_mul]; exact (ValuationRepresentative.vw_zero w).ge
    by_cases h1 : b = 0
    · rw [h1, mul_zero]; exact (ValuationRepresentative.vw_zero w).ge
    rw [ValuationRepresentative.vw_mul w a b h0 h1]
    exact add_nonneg ha hb
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    by_cases h0 : a = 0
    · rwa [h0, zero_add]
    by_cases h1 : b = 0
    · rwa [h1, add_zero]
    by_cases h2 : a + b = 0
    · rw [h2]; exact (ValuationRepresentative.vw_zero w).ge
    exact (le_min ha hb).trans (Formalism.PairingDivisionLocalBalance.vw_add w a b h0 h1 h2)
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    by_cases h0 : a = 0
    · rw [h0, neg_zero]; exact (ValuationRepresentative.vw_zero w).ge
    have h1 : 0 ≤ vw w (-1 : K) := by
      have := ValuationRepresentative.vw_int_nonneg w (-1 : 𝓞 K)
      simpa using this
    rw [← neg_one_mul, ValuationRepresentative.vw_mul w _ a (neg_ne_zero.2 one_ne_zero) h0]
    exact add_nonneg h1 ha

end

section

variable {K : Type} [Field K] (R : Subring K)

theorem mem_range_map_subtype_iff {σ : Type} (P : MvPolynomial σ K) :
    P ∈ (MvPolynomial.map (σ := σ) R.subtype).range ↔ ∀ m, AddMonoidAlgebra.coeff P m ∈ R := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    rw [coeff_map]
    exact (AddMonoidAlgebra.coeff Q m).2
  · intro h
    rw [P.as_sum]
    exact sum_mem fun m _ => ⟨monomial m ⟨_, h m⟩, by rw [map_monomial]; rfl⟩

theorem blockAct_mem_range_map_subtype {ι : Type} [Fintype ι] {n : ℕ}
    (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ R)
    {P : MvPolynomial (ι × Fin n × Fin n) K}
    (hP : P ∈ (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range) :
    Formalism.GradedWeylDivisibility.blockAct K U P ∈ (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range := by
  have hC : ∀ {a : K}, a ∈ R → (C a : MvPolynomial (ι × Fin n × Fin n) K) ∈
      (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range :=
    fun {a} ha => ⟨C ⟨a, ha⟩, by simp⟩
  have hX : ∀ v, (X v : MvPolynomial (ι × Fin n × Fin n) K) ∈
      (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range :=
    fun v => ⟨X v, by simp⟩
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, algHom_C]
    exact hC a.2
  | add p q hp hq =>
    rw [map_add (MvPolynomial.map R.subtype), map_add (f := _)]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul (MvPolynomial.map R.subtype), map_X, map_mul, blockAct_X]
    exact mul_mem hp (sum_mem fun b _ => mul_mem (hC (hU _ _ _)) (hX _))

end

theorem vw_fockS_blockAct_nonneg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (w : HeightOneSpectrum (𝓞 K)) (F F' : Pol K ι n) (U : ι → Matrix (Fin n) (Fin n) K), (∀ mo, 0 ≤ vw (conjPl w) (AddMonoidAlgebra.coeff F mo)) → (∀ mo, 0 ≤ vw w (AddMonoidAlgebra.coeff F' mo)) → (∀ τ a b, 0 ≤ vw w (U τ a b)) → 0 ≤ vw w (fockS F (Formalism.GradedWeylDivisibility.blockAct K U F')) := by
  intro K _ _ _ ι _ n w F F' U hF hF' hU
  have h := (mem_range_map_subtype_iff (nonnegRing_vw w) _).1
    (blockAct_mem_range_map_subtype (nonnegRing_vw w) U hU
      ((mem_range_map_subtype_iff (nonnegRing_vw w) F').2 hF'))
  change fockS F (Formalism.GradedWeylDivisibility.blockAct K U F') ∈ nonnegRing_vw w
  unfold fockS
  refine sum_mem fun m _ => mul_mem (mul_mem ?_ (h m)) (natCast_mem _ _)
  change 0 ≤ vw w (star (AddMonoidAlgebra.coeff F m))
  rw [ValuationRepresentative.vw_star]
  exact hF m

end GlobalTheory.TestLat
end

