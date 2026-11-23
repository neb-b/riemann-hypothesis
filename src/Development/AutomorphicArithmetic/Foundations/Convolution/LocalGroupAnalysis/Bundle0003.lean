module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
section
open PositivityTheory.Rg.Tf.Geo
open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_apply (σ : E ≃ₐ[F] E) (y : 𝔸[E]) : galAd σ y = σ • y := by
  have h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
    refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
      rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
      rfl
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
      rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        smul_adeleMap, map_one, map_one, one_mul]
      rfl
  rw [h]
  rfl

private theorem closedEmb (n : ℕ) : Topology.IsClosedEmbedding
    (mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n → AdelicGLn.AdelicGL E n) := by
  have hM : Topology.IsClosedEmbedding
      ((adeleMap F E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) 𝔸[F] → Matrix (Fin n) (Fin n) 𝔸[E]) :=
    Function.LeftInverse.isClosedEmbedding (f := fun M : Matrix (Fin n) (Fin n) 𝔸[E] => M.map (adeleRetraction F E))
      (fun M => Matrix.ext fun i j => adeleRetraction_adeleMap (M i j))
      (continuous_id.matrix_map continuous_adeleRetraction)
      (continuous_id.matrix_map continuous_adeleMap)
  exact @Topology.IsClosedEmbedding.units_map (AdelicGLn.AdelicMatrix F n) (AdelicGLn.AdelicMatrix E n)
    _ _ _ _ _ _ (adeleMap F E).mapMatrix.toMonoidHom hM

private theorem det_inc (n : ℕ) (g : AdelicGLn.AdelicGL F n) :
    AdelicGLn.det E n (mapGL n (adeleMap F E) g) = ideleEmbedding F E (AdelicGLn.det F n g) :=
  Units.ext ((adeleMap F E).map_det (g : Matrix (Fin n) (Fin n) 𝔸[F])).symm

private theorem det_gal (σ : E ≃ₐ[F] E) (n : ℕ) (g : AdelicGLn.AdelicGL E n) :
    AdelicGLn.det E n (mapGL n (galAd σ) g) = σ • (AdelicGLn.det E n g : IdeleGroup E) :=
  Units.ext ((((galAd σ).map_det (g : Matrix (Fin n) (Fin n) 𝔸[E])).symm).trans (galAd_apply σ _))

end

theorem UpperTheory.ConvolutionTheory.G.character_column_kernels_of_block_chi_c_of_block_chi_one :
    N5 := by
  intro F E _ _ _ _ _ _ σ _ n _
  refine ⟨closedEmb n, fun g => ?_, fun g => ?_⟩
  · change (IdeleGroup.ideleModule E (AdelicGLn.det E n (mapGL n (adeleMap F E) g)) : ℝ) =
      (IdeleGroup.ideleModule F (AdelicGLn.det F n g) : ℝ) ^ Module.finrank F E
    rw [det_inc, ← EllipticTorus.ideleModule_ideleNorm (K := F), ideleNorm_ideleEmbedding, map_pow,
      Positive.val_pow]
  · change IdeleGroup.ideleModule E (AdelicGLn.det E n (mapGL n (galAd σ) g)) =
      IdeleGroup.ideleModule E (AdelicGLn.det E n g)
    rw [det_gal, ← EllipticTorus.ideleModule_ideleNorm (K := F), ideleNorm_smul,
      EllipticTorus.ideleModule_ideleNorm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.CharpolyFactorCoeffZeroValuationEqProd
section
open PositivityTheory.Rg.Tf.Geo

open Polynomial

namespace UpperTheory.ConvolutionTheory.G.TA1

private lemma ext_val {k K Γ : Type*} [Field k] [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation k Γ) (f : k →+* K) :
    ∃ B : ValuationSubring K, (B.valuation.comap f).IsEquiv v := by
  obtain ⟨B, h, hl⟩ := IsLocalRing.exists_factor_valuationRing (f.comp v.valuationSubring.subtype)
  refine ⟨B, Valuation.isEquiv_iff_val_le_one.mpr fun {x} => ?_⟩
  rw [Valuation.comap_apply, B.valuation_le_one_iff]
  refine ⟨fun hx => ?_, fun hx => h ⟨x, hx⟩⟩
  by_contra hc
  push Not at hc
  have hx0 : x ≠ 0 := by rintro rfl; simp at hc
  have hi : v x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have hu : IsUnit (((f.comp v.valuationSubring.subtype).codRestrict B.toSubring h) ⟨x⁻¹, hi.le⟩) :=
    isUnit_iff_exists_inv.mpr ⟨⟨f x, hx⟩, Subtype.ext (by simp [hx0])⟩
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp (hl.1 _ hu)
  have hy' : x⁻¹ * (y : k) = 1 := congrArg Subtype.val hy
  have : (y : k) = x := by field_simp at hy'; exact hy'
  have h2 : v (y : k) ≤ 1 := y.2
  rw [this] at h2
  exact absurd hc (not_lt.mpr h2)

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {n : ℕ}

private lemma prod_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → K) (h : ∀ i, w (f i) ≤ 1) (i : ι)
    (hi : w (f i) < 1) : w (∏ j, f j) < 1 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, map_prod]
  exact mul_lt_one_of_lt_of_le hi (Finset.prod_le_one' fun j _ => h j)

private lemma det_sub (M : Matrix (Fin n) (Fin n) K) (h1 : ∀ i j, w (M i j) ≤ 1)
    (h2 : ∀ i j, j < i → w (M i j) < 1) : w (M.det - ∏ i, M i i) < 1 := by
  rw [Matrix.det_apply', ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
  simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply,
    add_sub_cancel_left]
  refine w.map_sum_lt one_ne_zero fun σ hσ => ?_
  have hσ1 : σ ≠ 1 := Finset.ne_of_mem_erase hσ
  have : ∃ i, i < σ i := by
    by_contra hc
    push Not at hc
    apply hσ1
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i => ((σ i : Fin n) : ℕ))
      (g := fun i : Fin n => (i : ℕ)) (fun i _ => hc i)).mp (Equiv.sum_comp σ (fun i : Fin n => (i : ℕ)))
    ext i
    simpa using this i (Finset.mem_univ i)
  obtain ⟨i, hi⟩ := this
  rw [map_mul]
  have hs : w ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]
  exact prod_lt w _ (fun j => h1 _ _) i (h2 _ _ hi)

private lemma scaled (t : Fin n → K) (ht0 : ∀ i, t i ≠ 0) (hinj : Function.Injective fun i => w (t i))
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ i j, w (u i j) ≤ 1) (h2 : ∀ i j, j < i → w (u i j) < 1)
    (h3 : ∀ i, w (u i i) = 1) (i : Fin n) :
    ∃ D : K, D ≠ 0 ∧ ∀ y : K, w y = 1 →
      (w (y - u i i) = 1 → w ((Matrix.diagonal t * u).charpoly.eval (t i * y)) = w D) ∧
      (y = u i i → w ((Matrix.diagonal t * u).charpoly.eval (t i * y)) < w D) := by
  classical
  let d : Fin n → K := fun j => if w (t j) < w (t i) then t i else t j
  have hd0 : ∀ j, d j ≠ 0 := fun j => by simp only [d]; split_ifs <;> exact ht0 _
  have hwt : ∀ j, 0 < w (t j) := fun j => by simpa [pos_iff_ne_zero] using ht0 j
  have hwd : ∀ j, 0 < w (d j) := fun j => by simpa [pos_iff_ne_zero] using hd0 j
  have hdi : ∀ j, w (t i / d j) ≤ 1 := fun j => by
    rw [map_div₀, div_le_one₀ (hwd j)]
    simp only [d]; split_ifs with h
    · exact le_rfl
    · exact not_lt.mp h
  have hdj : ∀ j, w (t j / d j) ≤ 1 := fun j => by
    rw [map_div₀, div_le_one₀ (hwd j)]
    simp only [d]; split_ifs with h
    · exact h.le
    · exact le_rfl
  refine ⟨∏ j, d j, Finset.prod_ne_zero_iff.mpr fun j _ => hd0 j, fun y hy => ?_⟩
  let M : Matrix (Fin n) (Fin n) K := Matrix.of fun j l =>
    (if j = l then t i / d j * y else 0) - t j / d j * u j l
  have hM : Matrix.scalar (Fin n) (t i * y) - Matrix.diagonal t * u = Matrix.diagonal d * M := by
    ext j l
    have := hd0 j
    simp only [M, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.of_apply]
    split_ifs
    · field_simp
    · field_simp; ring
  have hb : ∀ j l, w (t j / d j * u j l) ≤ 1 := fun j l => by
    rw [map_mul]; exact mul_le_one' (hdj j) (h1 j l)
  have hM1 : ∀ j l, w (M j l) ≤ 1 := fun j l => by
    refine w.map_sub_le ?_ (hb j l)
    split_ifs
    · rw [map_mul, hy, mul_one]; exact hdi j
    · simp
  have hM2 : ∀ j l, l < j → w (M j l) < 1 := fun j l h => by
    simp only [M, Matrix.of_apply, if_neg h.ne', zero_sub, Valuation.map_neg, map_mul]
    rw [mul_comm]; exact mul_lt_one_of_lt_of_le (h2 j l h) (hdj j)
  have hMi : M i i = y - u i i := by
    have := ht0 i
    simp [M, d, this]
  have hM3 : ∀ j, j ≠ i → w (M j j) = 1 := fun j hj => by
    have hne : w (t j) ≠ w (t i) := fun h => hj (hinj h)
    simp only [M, Matrix.of_apply, if_true, d]
    split_ifs with h
    · rw [div_self (ht0 i), one_mul, w.map_sub_eq_of_lt_left, hy]
      rw [hy, map_mul, h3, mul_one, map_div₀, div_lt_one₀ (hwt i)]; exact h
    · have h' : w (t i) < w (t j) := lt_of_le_of_ne (not_lt.mp h) hne.symm
      rw [div_self (ht0 j), one_mul, w.map_sub_eq_of_lt_right, h3]
      rw [h3, map_mul, hy, mul_one, map_div₀, div_lt_one₀ (hwt j)]; exact h'
  have hD : 0 < w (∏ j, d j) := by
    simpa [pos_iff_ne_zero, Finset.prod_ne_zero_iff] using hd0
  have hk := det_sub w M hM1 hM2
  rw [Matrix.eval_charpoly, hM, Matrix.det_mul, Matrix.det_diagonal, map_mul]
  constructor
  · intro h
    have hp : w (∏ j, M j j) = 1 := by
      rw [map_prod]
      refine Finset.prod_eq_one fun j _ => ?_
      by_cases hj : j = i
      · rw [hj, hMi, h]
      · exact hM3 j hj
    have : w M.det = 1 := by
      rw [← hp] at hk ⊢
      exact w.map_eq_of_sub_lt hk
    rw [this, mul_one]
  · intro h
    have hp : ∏ j, M j j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hMi, h, sub_self])
    rw [hp, sub_zero] at hk
    exact mul_lt_of_lt_one_right hD hk

private lemma exists_unit [IsAlgClosed K] (c : K) (hc : w c = 1) : ∃ y, w y = 1 ∧ w (y - c) = 1 := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (X * (X - C c) - 1 : K[X]) (by
    have : (X * (X - C c) - 1 : K[X]).degree = 2 := by compute_degree!
    rw [this]; decide)
  have h : w y * w (y - c) = 1 := by
    rw [← map_mul]
    have : y * (y - c) = 1 := by simpa [sub_eq_zero] using hy
    rw [this, map_one]
  have h1 : w y = 1 := by
    rcases lt_trichotomy (w y) 1 with h' | h' | h'
    · rw [w.map_sub_eq_of_lt_right (by rwa [hc]), hc, mul_one] at h; exact h
    · exact h'
    · rw [w.map_sub_eq_of_lt_left (by rwa [hc])] at h
      exact absurd h (one_lt_mul'' h' h').ne'
  exact ⟨y, h1, by simpa [h1] using h⟩

private lemma exists_root [IsAlgClosed K] (t : Fin n → K) (ht0 : ∀ i, t i ≠ 0)
    (hinj : Function.Injective fun i => w (t i))
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ i j, w (u i j) ≤ 1) (h2 : ∀ i j, j < i → w (u i j) < 1)
    (h3 : ∀ i, w (u i i) = 1) (i : Fin n) :
    ∃ r ∈ (Matrix.diagonal t * u).charpoly.roots, w r = w (t i) := by
  by_contra hc
  push Not at hc
  obtain ⟨D, -, hD⟩ := scaled w t ht0 hinj u h1 h2 h3 i
  obtain ⟨y, hy, hy'⟩ := exists_unit w (u i i) (h3 i)
  have e1 := (hD y hy).1 hy'
  have e2 := (hD _ (h3 i)).2 rfl
  have key : ∀ z : K, w z = 1 → w ((Matrix.diagonal t * u).charpoly.eval (t i * z)) =
      ((Matrix.diagonal t * u).charpoly.roots.map fun r => max (w (t i)) (w r)).prod := fun z hz => by
    rw [(IsAlgClosed.splits _).eval_eq_prod_roots_of_monic (Matrix.charpoly_monic _), map_multiset_prod,
      Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun r hr => ?_
    have hz' : w (t i * z) = w (t i) := by rw [map_mul, hz, mul_one]
    rcases lt_or_gt_of_ne (hc r hr) with h | h
    · rw [Function.comp_apply, w.map_sub_eq_of_lt_left (by rwa [hz']), hz', max_eq_left h.le]
    · rw [Function.comp_apply, w.map_sub_eq_of_lt_right (by rwa [hz']), max_eq_right h.le]
  rw [key _ hy] at e1
  rw [key _ (h3 i), e1] at e2
  exact lt_irrefl _ e2

private lemma main [IsAlgClosed K] (t : Fin n → K) (ht0 : ∀ i, t i ≠ 0)
    (hinj : Function.Injective fun i => w (t i))
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ i j, w (u i j) ≤ 1) (h2 : ∀ i j, j < i → w (u i j) < 1)
    (h3 : ∀ i, w (u i i) = 1) (p : K[X]) (hp : p.Monic) (hd : p ∣ (Matrix.diagonal t * u).charpoly) :
    ∃ J : Finset (Fin n), J.card = p.natDegree ∧ w (p.coeff 0) = w (∏ i ∈ J, t i) := by
  classical
  choose r hr hrw using exists_root w t ht0 hinj u h1 h2 h3
  have hri : Function.Injective r := fun i j h => hinj (by simp only [← hrw, h])
  have hle : (Finset.univ.val.map r) ≤ (Matrix.diagonal t * u).charpoly.roots := by
    rw [Multiset.le_iff_subset (Finset.univ.nodup.map hri)]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact hr i
  have heq : (Finset.univ.val.map r) = (Matrix.diagonal t * u).charpoly.roots := by
    refine Multiset.eq_of_le_of_card_le hle ?_
    have := card_roots' (Matrix.diagonal t * u).charpoly
    simpa using this
  have hpl : p.roots ≤ Finset.univ.val.map r :=
    heq ▸ roots.le_of_dvd (Matrix.charpoly_monic _).ne_zero hd
  have hJ : p.roots = (Finset.univ.filter fun i => r i ∈ p.roots).val.map r := by
    refine (Multiset.Nodup.ext (Multiset.nodup_of_le hpl (Finset.univ.nodup.map hri))
      ((Finset.nodup _).map hri)).mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le hpl hx)
      exact Multiset.mem_map.mpr ⟨i, by simpa using hx, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
      simpa using hi
  refine ⟨Finset.univ.filter fun i => r i ∈ p.roots, ?_, ?_⟩
  · rw [(IsAlgClosed.splits p).natDegree_eq_card_roots]
    conv_rhs => rw [hJ]
    rw [Multiset.card_map]; rfl
  · rw [(IsAlgClosed.splits p).coeff_zero_eq_prod_roots_of_monic hp, map_mul, map_pow, Valuation.map_neg,
      map_one, one_pow, one_mul, map_prod]
    conv_lhs => rw [hJ]
    rw [← Finset.prod_eq_multiset_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => hrw i

end UpperTheory.ConvolutionTheory.G.TA1

open UpperTheory.ConvolutionTheory.G.TA1 GroundTheory.Automorphic in
theorem UpperTheory.ConvolutionTheory.G.charpoly_factor_coeff_zero_valuation_eq_prod :
    A1 := by
  intro k _ _ _ _ n μ hμ a ha b hb p hp hd
  obtain ⟨h1, h2, h3⟩ := (GLnLocal.mem_iwahori_iff k n).mp ((GLnLocal.iwahori k n).mul_mem hb ha)
  let f : k →+* AlgebraicClosure k := algebraMap _ _
  obtain ⟨B, hB⟩ := ext_val (ValuativeRel.valuation k) f
  have hd' : p ∣ (Matrix.diagonal (fun i => (GLnLocal.uniformizer k : k) ^ μ i) *
      ((b * a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).charpoly := by
    rwa [Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Cartan.coe_diagPow,
      Matrix.mul_assoc, ← Units.val_mul] at hd
  have hπ := Cartan.uniformizer_ne_zero k
  obtain ⟨J, hJ, hv⟩ := main B.valuation (fun i => f ((GLnLocal.uniformizer k : k) ^ μ i))
    (fun i => (map_ne_zero f).mpr (zpow_ne_zero _ hπ))
    (fun i j h => by
      have h' := (hB.eq_iff).mp h
      simp only [map_zpow₀] at h'
      exact hμ (zpow_right_injective₀ (GLnLocal.valuation_uniformizer_pos k)
        (GLnLocal.valuation_uniformizer_lt_one k).ne h'))
    (((b * a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map f)
    (fun i j => (hB.le_one_iff_le_one).mpr (h1 i j))
    (fun i j h => (hB.lt_one_iff_lt_one).mpr (h2 i j h))
    (fun i => (hB.eq_one_iff_eq_one).mpr (h3 i)) (p.map f) (hp.map f) (by
      have := Polynomial.map_dvd f hd'
      rwa [← Matrix.charpoly_map, Matrix.map_mul, Matrix.diagonal_map (map_zero f)] at this)
  refine ⟨J, by rw [hJ, natDegree_map], ?_⟩
  rw [coeff_map, ← map_prod] at hv
  simp only [Cartan.coe_diagPow, Matrix.diagonal_apply_eq]
  exact (hB.eq_iff).mp hv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.ClosedSubgroupCutoffExists
section
open PositivityTheory.Rg.Tf.Geo
open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

private theorem exists_bump {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    (H : Subgroup X) (hH : IsClosed (H : Set X)) :
    ∃ β : X → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧ (∀ x, ∃ h ∈ H, β (h * x) ≠ 0) ∧
      ∀ C : Set X, IsCompact C → ∃ C' : Set X, IsCompact C' ∧
        ∀ h ∈ H, ∀ x ∈ C, β (h * x) ≠ 0 → h * x ∈ C' := by
  classical
  let K : CompactExhaustion X := (CompactExhaustion.choice X).shiftr.shiftr
  have hK0 : K 0 = ∅ := rfl
  have hK1 : K 1 = ∅ := rfl
  let S : ℕ → Set X := fun m => (H : Set X) * K m
  let O : ℕ → Set X := fun m => (H : Set X) * interior (K m)
  have hSc : ∀ m, IsClosed (S m) := fun m => hH.mul_right_of_isCompact (K.isCompact m)
  have hOo : ∀ m, IsOpen (O m) := fun m => isOpen_interior.mul_left
  have hQ : ∀ m, IsCompact (K (m + 2) \ O (m + 1)) := fun m => (K.isCompact _).diff (hOo _)
  have hSO : ∀ m, S m ⊆ O (m + 1) := fun m => Set.mul_subset_mul_left (K.subset_interior_succ m)
  have hd : ∀ m, Disjoint (K (m + 2) \ O (m + 1)) (S m) := fun m =>
    Set.disjoint_left.2 fun x hx hxS => hx.2 (hSO m hxS)
  choose f hf1 hf0 hfc hfI using fun m =>
    exists_continuous_one_zero_of_isCompact (hQ m) (hSc m) (hd m)
  have hself : ∀ m, K m ⊆ S m := fun m x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩
  have hSmono : ∀ {a b : ℕ}, a ≤ b → S a ⊆ S b := fun hab =>
    Set.mul_subset_mul_left (K.subset hab)
  have hvan : ∀ {N m : ℕ}, N ≤ m → ∀ x ∈ S N, f m x = 0 := fun hNm x hx => hf0 _ (hSmono hNm hx)
  have hnn : ∀ m x, 0 ≤ f m x := fun m x => (hfI m x).1
  have hlf : LocallyFinite fun m => Function.support (f m) := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine ⟨interior (K (n + 1)), isOpen_interior.mem_nhds (K.subset_interior_succ n hn),
      (Set.finite_lt_nat (n + 1)).subset ?_⟩
    rintro m ⟨y, hy, hyU⟩
    by_contra hm
    exact hy (hvan (not_lt.1 hm) y (hself _ (interior_subset hyU)))
  have hfin : ∀ x, (Function.support fun m => f m x).Finite := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine (Set.finite_lt_nat n).subset ?_
    intro m hm
    by_contra hmn
    exact hm (hvan (not_lt.1 hmn) x (hself _ hn))
  refine ⟨fun x => ∑ᶠ m, f m x, continuous_finsum (fun m => (f m).continuous) hlf,
    fun x => finsum_nonneg fun m => hnn m x, ?_, ?_⟩
  · intro x
    have hex : ∃ n, x ∈ O n := by
      obtain ⟨n, hn⟩ := K.exists_mem x
      exact ⟨n + 1, 1, H.one_mem, x, K.subset_interior_succ n hn, one_mul x⟩
    have hspec := Nat.find_spec hex
    have hmin : ∀ n, n < Nat.find hex → x ∉ O n := fun n hn => Nat.find_min hex hn
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 2 := by
      rcases hN : Nat.find hex with _ | _ | m
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK0] at hy
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK1] at hy
      · exact ⟨m, rfl⟩
    rw [hm] at hspec
    obtain ⟨h, hh, y, hy, rfl⟩ := hspec
    have hyQ : y ∈ K (m + 2) \ O (m + 1) := by
      refine ⟨interior_subset hy, ?_⟩
      rintro ⟨h', hh', z, hz, rfl⟩
      refine hmin (m + 1) (by omega) ⟨h * h', H.mul_mem hh hh', z, hz, (mul_assoc _ _ _)⟩
    refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
    rw [inv_mul_cancel_left]
    have h1 : f m y ≤ ∑ᶠ m, f m y := single_le_finsum m (hfin y) (fun j => hnn j y)
    have h2 : f m y = 1 := hf1 m hyQ
    intro h0
    simp only [h0, h2] at h1
    linarith
  · intro C hC
    obtain ⟨N, hN⟩ := K.exists_superset_of_isCompact hC
    refine ⟨⋃ m ∈ Finset.range N, tsupport (f m),
      (Finset.range N).isCompact_biUnion fun m _ => hfc m, ?_⟩
    intro h hh x hx hne
    obtain ⟨m, hm⟩ : ∃ m, f m (h * x) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (finsum_eq_zero_of_forall_eq_zero hall)
    have hmN : m < N := by
      by_contra hmN
      exact hm (hvan (not_lt.1 hmN) _ ⟨h, hh, x, hN hx, rfl⟩)
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hmN)) (subset_tsupport _ hm)

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.closedSubgroup_cutoff_exists :
    Q2 := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ν _ _ i hi
  have hH : IsClosed ((i.range : Subgroup X) : Set X) := by
    rw [MonoidHom.coe_range]; exact hi.isClosed_range
  obtain ⟨β, hβ, hβ0, hcov, hsupp⟩ := UpperTheory.ConvolutionTheory.G.exists_bump i.range hH
  have hB : ∀ C : Set X, IsCompact C → ∃ B : Set T, IsCompact B ∧
      ∀ t, ∀ x ∈ C, β (i t * x) ≠ 0 → t ∈ B := by
    intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨i ⁻¹' (C' * C⁻¹), hi.isCompact_preimage (hC'.mul hC.inv), fun t x hx hne => ?_⟩
    exact ⟨i t * x, h _ ⟨t, rfl⟩ x hx hne, x⁻¹, Set.inv_mem_inv.2 hx, by simp⟩
  have hc : Continuous (Function.uncurry fun (x : X) (t : T) => β (i t * x)) :=
    hβ.comp ((hi.continuous.comp continuous_snd).mul continuous_fst)
  have hcx : ∀ x, Continuous fun t => β (i t * x) := fun x =>
    hβ.comp (hi.continuous.mul continuous_const)
  have hcs : ∀ x, HasCompactSupport fun t => β (i t * x) := by
    intro x
    obtain ⟨B, hBc, hB'⟩ := hB {x} isCompact_singleton
    refine HasCompactSupport.intro hBc fun t ht => ?_
    by_contra hne
    exact ht (hB' t x rfl hne)
  let D : X → ℝ := fun x => ∫ t, β (i t * x) ∂ν
  have hDc : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
    obtain ⟨B, hBc, hB'⟩ := hB N hNc
    have h1 : Continuous fun x => ∫ t in B, β (i t * x) ∂ν :=
      continuous_parametric_integral_of_continuous hc hBc
    refine h1.continuousAt.congr ?_
    filter_upwards [hN] with x hx
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    by_contra hne
    exact ht (hB' t x hx hne)
  have hDpos : ∀ x, 0 < D x := by
    intro x
    obtain ⟨h, ⟨t₀, rfl⟩, hne⟩ := hcov x
    exact (hcx x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun t => hβ0 _) hne
  have hDinv : ∀ s x, D (i s * x) = D x := by
    intro s x
    have := integral_mul_right_eq_self (μ := ν) (fun t => β (i t * x)) s
    simpa [D, mul_assoc] using this
  refine ⟨fun x => Real.toNNReal (β x / D x),
    continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'), ⟨?_, ?_⟩, ?_⟩
  · exact (ENNReal.continuous_coe.comp
      (continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'))).measurable
  · intro x
    have hint : Integrable (fun t => β (i t * x) / D x) ν :=
      ((hcx x).integrable_of_hasCompactSupport (hcs x)).div_const _
    have h1 : ∫⁻ t, ((Real.toNNReal (β (i t * id x) / D (i t * id x)) : NNReal) : ℝ≥0∞) ∂ν =
        ∫⁻ t, ENNReal.ofReal (β (i t * x) / D x) ∂ν := by
      refine lintegral_congr fun t => ?_
      simp only [id, hDinv]
      rfl
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => div_nonneg (hβ0 _) (hDpos x).le), integral_div]
    change ENNReal.ofReal (D x / D x) = 1
    rw [div_self (hDpos x).ne', ENNReal.ofReal_one]
  · intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨C', hC', fun t x hx hne => h _ ⟨t, rfl⟩ x hx fun h0 => hne ?_⟩
    simp [h0]
end

