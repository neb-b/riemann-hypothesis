module

public import Mathlib
public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
public import ReciprocityTheory.SemistableReduction.Bundle0007
public import ReciprocityTheory.SemistableReduction.Bundle0008
public import Lemmata.GeneralBFactBisAlt.Imports
public import ReciprocityTheory.SemistableReduction.Bundle0006
public import ReciprocityTheory.SemistableReduction.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.CauchyInequalityOnTorus
section
namespace ReciprocityTheory.MultiplicativeHeights

theorem cauchy_inequality_on_torus : CauchyTorusStatement := by
  intro K _ _ _ K₀ hK₀ n c hc hτ χ
  by_contra hχ
  push_neg at hχ
  have hev : ∀ᶠ ψ in Filter.cofinite, ‖c ψ‖ < 1 / 2 := hc.eventually (gt_mem_nhds (by norm_num))
  have hFfin : {ψ | ¬ ‖c ψ‖ < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  set F := hFfin.toFinset with hFdef
  have hχF : χ ∈ F := by
    rw [Set.Finite.mem_toFinset]
    show ¬ ‖c χ‖ < 1 / 2
    linarith
  obtain ⟨χm, hχmF, hmax⟩ := F.exists_max_image (fun ψ => ‖c ψ‖) ⟨χ, hχF⟩
  have hgt : 1 < ‖c χm‖ := lt_of_lt_of_le hχ (hmax χ hχF)
  have hglob : ∀ ψ, ‖c ψ‖ ≤ ‖c χm‖ := by
    intro ψ
    by_cases hψ : ψ ∈ F
    · exact hmax ψ hψ
    · have h2 : ‖c ψ‖ < 1 / 2 := by
        rw [Set.Finite.mem_toFinset] at hψ
        simpa using hψ
      linarith
  set lam := c χm with hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgt
    linarith
  set a : (Fin n → ℤ) → K := fun ψ => c ψ / lam with hadef
  have ha : ∀ ψ, ‖a ψ‖ ≤ 1 := by
    intro ψ
    simp only [hadef, norm_div]
    exact (div_le_one (norm_pos_iff.2 hlam0)).2 (hglob ψ)
  have ha0 : ‖a χm‖ = 1 := by
    simp only [hadef, norm_div]
    exact div_self (norm_ne_zero_iff.2 hlam0)
  obtain ⟨τ, hτu, hτ1⟩ := exists_torus_point_one_le_norm_sum K₀ hK₀ F a ha χm hχmF ha0
  have hprodnorm : ∀ ψ : Fin n → ℤ, ‖∏ i, τ i ^ ψ i‖ = 1 := by
    intro ψ
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [norm_zpow, (hτu i).2, one_zpow]
  have hSF : ∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i = lam * ∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [hadef]
    field_simp
  have hSFn : ‖lam‖ ≤ ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ := by
    rw [hSF, norm_mul]
    calc ‖lam‖ = ‖lam‖ * 1 := (mul_one _).symm
      _ ≤ ‖lam‖ * ‖∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i‖ := mul_le_mul_of_nonneg_left hτ1 (norm_nonneg _)
  have hsum : Summable (fun ψ => c ψ * ∏ i, τ i ^ ψ i) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_mul, hprodnorm] using hc
  have hsplit := hsum.sum_add_tsum_compl (s := F)
  have htail : ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ ≤ 1 / 2 := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun ψ => ?_
    rw [norm_mul, hprodnorm, mul_one]
    have hψ : (ψ : Fin n → ℤ) ∉ F := fun h => ψ.2 (Finset.mem_coe.2 h)
    rw [Set.Finite.mem_toFinset] at hψ
    simp only [Set.mem_setOf_eq, not_not] at hψ
    exact le_of_lt hψ
  have hne : ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ ≠
      ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ := by
    intro h
    linarith
  have htot := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [hsplit] at htot
  have h1 := hτ τ hτu
  unfold torusSum at h1
  rw [htot] at h1
  have h3 := le_max_left ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖
    ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖
  linarith

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.EmbMatMulVecInjective
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DegAdd

open Matrix NumberField
open scoped ComplexOrder

def embMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (v : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a j => σ (v j a)

theorem gramC_eq_mul {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (v : Fin k → Fin r → K) :
    gramC H σ v = (embMat σ v)ᴴ * H * embMat σ v := by
  ext i j
  simp only [gramC, embMat, embVec, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

theorem embMat_mulVec_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    {v : Fin k → Fin r → K} (hv : LinearIndependent K v) :
    Function.Injective (embMat σ v).mulVec := by
  set B : Matrix (Fin r) (Fin k) K := Matrix.of fun a j => v j a
  have hcol : B.col = v := by
    funext j a
    rfl
  have hB : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hv
  have hker : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact hB (by simpa [Matrix.toLin'_apply] using h)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) hker
  have hNB : LinearMap.toMatrix' g * B = 1 := by
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hE : embMat σ v = B.map σ := rfl
  have h1 : (LinearMap.toMatrix' g).map σ * embMat σ v = 1 := by
    rw [hE, ← Matrix.map_mul, hNB, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have h := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, h1] using h

theorem gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) {v : Fin k → Fin r → K} (hH : H.PosDef)
    (hv : LinearIndependent K v) : (gramC H σ v).PosDef := by
  rw [gramC_eq_mul]
  exact hH.conjTranspose_mul_mul_same (embMat_mulVec_injective σ hv)

theorem gramC_append_blocks {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) :
    (gramC H σ (Fin.append b c)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (gramC H σ b) (gramX H σ b c) (gramX H σ c b) (gramC H σ c) := by
  ext (i | i) (j | j) <;> simp [gramC, gramX]

theorem log_det_gram_append {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) (hH : H.PosDef) (hb : LinearIndependent K b)
    (h : LinearIndependent K (Fin.append b c)) :
    Real.log (gramC H σ (Fin.append b c)).det.re =
      Real.log (gramC H σ b).det.re + Real.log (quotGramC H σ b c).det.re := by
  have hG := (gramC_posDef H σ hH h).det_pos
  have hGb := (gramC_posDef H σ hH hb).det_pos
  have : Invertible (gramC H σ b) := (gramC_posDef H σ hH hb).isUnit.invertible
  have hdet : (gramC H σ (Fin.append b c)).det =
      (gramC H σ b).det * (quotGramC H σ b c).det := by
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv (gramC H σ (Fin.append b c)),
      gramC_append_blocks, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    rfl
  rw [hdet] at hG ⊢
  rw [Complex.pos_iff] at hG hGb
  have hre : ((gramC H σ b).det * (quotGramC H σ b c).det).re =
      (gramC H σ b).det.re * (quotGramC H σ b c).det.re := by
    simp [Complex.mul_re, ← hGb.2]
  have hy : 0 < (quotGramC H σ b c).det.re := by
    rw [hre] at hG
    exact (pos_iff_pos_of_mul_pos hG.1).mp hGb.1
  rw [hre, Real.log_mul hGb.1.ne' hy.ne']

end DegAdd

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.ExistsIntSmulMemSpan
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DegAdd

open NumberField

theorem exists_int_smul_mem_span {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (v : Fin n → Fin r → K) {x : Fin r → K} (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range v) := by
  first | exact Bl.general_b_fact_bis_other.goal1 .. | (apply Bl.general_b_fact_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_other.goal1 <;> assumption)

theorem relIndex_ne_zero_of_fg {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : L.FG) (v : Fin n → Fin r → K)
    (hv : ∀ x ∈ L, x ∈ Submodule.span K (Set.range v)) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
  set N := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.addSubgroupOf L.toAddSubgroup
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  let f : L →+ (L.toAddSubgroup ⧸ N) :=
    { toFun := fun x => QuotientAddGroup.mk (⟨x.1, x.2⟩ : L.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : Module.Finite ℤ (L.toAddSubgroup ⧸ N) := by
    refine Module.Finite.of_surjective f.toIntLinearMap ?_
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨⟨y, hy⟩, rfl⟩
  have : Finite (L.toAddSubgroup ⧸ N) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨d, hd, hdy⟩ := exists_int_smul_mem_span v (hv y hy)
    refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
    change (d • (QuotientAddGroup.mk (⟨y, hy⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸ N)) = 0
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hdy
  exact AddSubgroup.index_ne_zero_of_finite

theorem range_fin_append {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Set.range (Fin.append b c) = Set.range b ∪ Set.range c := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, (Fin.append_left b c i).symm⟩
    | right j => exact Or.inr ⟨j, (Fin.append_right b c j).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd m i, Fin.append_left b c i⟩
    · exact ⟨Fin.natAdd k j, Fin.append_right b c j⟩

theorem fin_append_comp_equiv {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Fin.append b c ∘ finSumFinEquiv = Sum.elim b c := by
  funext i
  cases i <;> simp

theorem indep_parts {K : Type} [Field K] {r k m : ℕ}
    {b : Fin k → Fin r → K} {c : Fin m → Fin r → K} (h : LinearIndependent K (Fin.append b c)) :
    LinearIndependent K b ∧ LinearIndependent K c ∧
      Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c)) := by
  have h2 := h.comp finSumFinEquiv finSumFinEquiv.injective
  rw [fin_append_comp_equiv] at h2
  have h3 := linearIndependent_sum.mp h2
  simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr] using h3

theorem index_split {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hb : ∀ i, b i ∈ L) (hc : ∀ j, c j ∈ L)
    (hdis : Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c))) :
    (Submodule.span (𝓞 K) (Set.range (Fin.append b c))).toAddSubgroup.relIndex L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex (satSub L b).toAddSubgroup *
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
        L.toAddSubgroup := by
  set Sb := Submodule.span (𝓞 K) (Set.range b)
  set Sc := Submodule.span (𝓞 K) (Set.range c)
  set S := satSub L b
  have hA : Submodule.span (𝓞 K) (Set.range (Fin.append b c)) = Sb ⊔ Sc := by
    rw [range_fin_append, Submodule.span_union]
  have hSbS : Sb ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨hb i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hScL : Sc ≤ L := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hc j
  have hSL : S ≤ L := inf_le_left
  have hmeet : ∀ x, x ∈ Sb ⊔ Sc → x ∈ S → x ∈ Sb := by
    intro x hx1 hx2
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx1
    have hyK : y ∈ Submodule.span K (Set.range b) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hy
    have hzK : z ∈ Submodule.span K (Set.range c) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hz
    have hxK : y + z ∈ Submodule.span K (Set.range b) := hx2.2
    have hz' : z ∈ Submodule.span K (Set.range b) := by
      have h := Submodule.sub_mem _ hxK hyK
      simpa using h
    have hz0 : z = 0 := Submodule.disjoint_def.mp hdis z hz' hzK
    simpa [hz0] using hy
  have hinf : (Sb ⊔ Sc).toAddSubgroup ⊓ S.toAddSubgroup = Sb.toAddSubgroup := by
    ext x
    constructor
    · intro h
      exact hmeet x (AddSubgroup.mem_inf.mp h).1 (AddSubgroup.mem_inf.mp h).2
    · intro h
      exact AddSubgroup.mem_inf.mpr ⟨(le_sup_left : Sb ≤ Sb ⊔ Sc) h, hSbS h⟩
  have key : (Sb ⊔ Sc).toAddSubgroup.relIndex (S ⊔ Sc).toAddSubgroup =
      Sb.toAddSubgroup.relIndex S.toAddSubgroup := by
    have hsup : (S ⊔ Sc).toAddSubgroup = S.toAddSubgroup ⊔ (Sb ⊔ Sc).toAddSubgroup := by
      rw [← Submodule.sup_toAddSubgroup, ← sup_assoc, sup_eq_left.mpr hSbS]
    rw [hsup, AddSubgroup.relIndex_sup_right, ← hinf, AddSubgroup.inf_relIndex_right]
  have le1 : (Sb ⊔ Sc).toAddSubgroup ≤ (S ⊔ Sc).toAddSubgroup :=
    fun x hx => (sup_le_sup_right hSbS Sc) hx
  have le2 : (S ⊔ Sc).toAddSubgroup ≤ L.toAddSubgroup := fun x hx => (sup_le hSL hScL) hx
  rw [hA, ← AddSubgroup.relIndex_mul_relIndex _ _ _ le1 le2, key]

end DegAdd

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.GaussExtensionAndResidueTrdegEq
section
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

theorem residueTrdeg_holds (hTR : TRStatement) : ResidueTrdegStatement := by
  intro K Ω U _ _ _ _ _ D hD σ _ t V ht τ _ u p hp hcard hpu hind
  letI _iW := residueAlgebra V (algebraMap Ω U)
  letI _io := residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
  letI : Algebra (IsLocalRing.ResidueField
      ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
    ((algebraMap _ (IsLocalRing.ResidueField V)).comp
      (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
  have hTRW := hTR K Ω (V.comap (algebraMap Ω U))
  rw [hD] at hTRW
  have hST : IsScalarTower
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) (IsLocalRing.ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hres : ∀ j, IsLocalRing.residue V (u j) =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V (p j) (hp j)) := by
    intro j
    obtain ⟨h, he⟩ := gaussRed_eval t V ht (p j) (hp j)
    have : u j = ⟨aeval t (p j), h⟩ := Subtype.ext (hpu j).symm
    rw [this, he]
  have hcardc : Cardinal.mk τ = ((Fintype.card σ + D : ℕ) : Cardinal) := by
    rw [Cardinal.mk_fintype, hcard]
  have hσ := Cardinal.mk_fintype σ
  have hmemW : ∀ j, IsLocalRing.residue V (u j) ∈
      Algebra.adjoin (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (Set.range fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := by
    intro j
    rw [hres j]
    exact gauss_aeval_mem _ _ (Algebra.adjoin _ _).toSubring
      (fun α => Subalgebra.algebraMap_mem _ _) (fun s => Algebra.subset_adjoin ⟨s, rfl⟩)
  have hW := gauss_card_le_trdeg_add _ _ hind hmemW
  rw [hcardc] at hW
  obtain ⟨h2, h3⟩ := gauss_card_arith hW hTRW (hσ ▸ gauss_trdeg_adjoin_le _)
  refine ⟨?_, h2, gauss_indep_of_le_trdeg _ (hσ.trans h3.symm).le⟩
  intro k₁ hk₁
  letI : Algebra k₁ (IsLocalRing.ResidueField V) :=
    ((algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
      (IsLocalRing.ResidueField V)).comp (algebraMap k₁ _)).toAlgebra
  have hST1 : IsScalarTower
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      k₁ (IsLocalRing.ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmem1 : ∀ j, IsLocalRing.residue V (u j) ∈
      Algebra.adjoin k₁ (Set.range fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := by
    intro j
    rw [hres j]
    refine gauss_aeval_mem _ _ (Algebra.adjoin k₁ _).toSubring (fun α => ?_)
      (fun s => Algebra.subset_adjoin ⟨s, rfl⟩)
    have hc : (gaussRed V (p j) (hp j)).coeff α ∈ k₁ := by
      rw [gaussRed_coeff]; exact hk₁ j α
    exact Subalgebra.algebraMap_mem (Algebra.adjoin k₁ _) (⟨_, hc⟩ : k₁)
  have h1 := @gauss_card_le_trdeg_add _ _ _ _ _ _ _ _ _ hST1 _ _ _ _ hind hmem1
  rw [hcardc] at h1
  have hk : Algebra.trdeg _ k₁ ≤ (D : Cardinal) :=
    (trdeg_le_of_injective k₁.val Subtype.val_injective).trans hTRW
  exact (gauss_card_arith h1 hk (hσ ▸ gauss_trdeg_adjoin_le _)).1

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.GenericImageFinite
section
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial DerivationAlgebraicIndependence

theorem trdeg_sField {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ) :
    Algebra.trdeg K (SField Ω D m) = Algebra.trdeg K Ω + ((1 + (D + 1) * m : ℕ) : Cardinal) := by
  classical
  haveI : FaithfulSMul K Ω :=
    (faithfulSMul_iff_algebraMap_injective K Ω).2 (algebraMap K Ω).injective
  haveI : FaithfulSMul Ω (MvPolynomial (SVars D m) Ω) :=
    (faithfulSMul_iff_algebraMap_injective Ω _).2 (MvPolynomial.C_injective _ _)
  haveI : FaithfulSMul (MvPolynomial (SVars D m) Ω) (SField Ω D m) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (IsFractionRing.injective (MvPolynomial (SVars D m) Ω) (SField Ω D m))
  have h1 := trdeg_add_eq K (MvPolynomial (SVars D m) Ω) (A := SField Ω D m)
  have h2 := trdeg_add_eq K Ω (A := MvPolynomial (SVars D m) Ω)
  have h3 : Algebra.trdeg (MvPolynomial (SVars D m) Ω) (SField Ω D m) = 0 :=
    trdeg_eq_zero_iff.2
      (IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (SVars D m) Ω)))
  have h4 : Algebra.trdeg Ω (MvPolynomial (SVars D m) Ω) =
      ((1 + (D + 1) * m : ℕ) : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
    congr 1
    simp [SVars, Fintype.card_sum, Fintype.card_prod]
  rw [← h1, h3, add_zero, ← h2, h4]

theorem genericImageFinite : FieldOfSStatement := by
  classical
  unfold FieldOfSStatement
  intro K Ω _ _ _ _ D m x hfg htr hJ
  obtain ⟨J, hJ⟩ := hJ
  set v : Fin D → KaehlerDifferential K Ω := fun a => KaehlerDifferential.D K Ω (x (J a)) with hv
  have hli : LinearIndependent Ω v := hJ
  have hφ : ∀ a : Fin D, ∃ φ : KaehlerDifferential K Ω →ₗ[Ω] Ω,
      ∀ b, φ (v b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply a).comp hli.repr)
    refine ⟨g, fun b => ?_⟩
    have hb : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
    have h := congrArg (fun f => f ⟨v b, hb⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, Finsupp.lapply_apply, hli.repr_eq_single b ⟨v b, hb⟩ rfl, Finsupp.single_apply]
    simp [eq_comm]
  choose φ hφ using hφ
  let δ : Fin D → Derivation K Ω Ω := fun a => (φ a).compDer (KaehlerDifferential.D K Ω)
  have hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := fun a b => hφ a b
  have hg := DerivationAlgebraicIndependence.gFam_indep (K := K) x J δ hδ
  have hind : AlgebraicIndependent K (sImage (D := D) x) := by
    have h1 := hg.comp _ (DerivationAlgebraicIndependence.eIdx_injective D m)
    have h2 := h1.map'
      (f := IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m))
      (IsFractionRing.injective _ _)
    convert h2 using 1
    funext p
    simp [DerivationAlgebraicIndependence.sImage_eq]
  refine ⟨hind, ?_⟩
  have htrS : Algebra.trdeg K (SField Ω D m) = (((D + 1) * (m + 1) : ℕ) : Cardinal) := by
    rw [trdeg_sField, htr, ← Nat.cast_add]
    congr 1
    ring
  have hTB : IsTranscendenceBasis K (sImage (D := D) x) := by
    refine hind.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_
    · rw [htrS]
      exact Cardinal.natCast_lt_aleph0
    · rw [htrS]
      simp
  have halg := hTB.isAlgebraic_field
  set E := IntermediateField.adjoin K (Set.range (sImage (D := D) x))
  obtain ⟨s, hs⟩ := hfg
  let f : Ω →ₐ[K] SField Ω D m :=
    (IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m)).comp
      (IsScalarTower.toAlgHom K Ω (MvPolynomial (SVars D m) Ω))
  let S : Set (SField Ω D m) := f '' (s : Set Ω) ∪
    Set.range (fun i => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (MvPolynomial.X i))
  have hSfin : S.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  haveI : Finite S := hSfin.to_subtype
  let L := IntermediateField.adjoin E S
  have hK : IntermediateField.adjoin K (f '' (s : Set Ω)) ≤ L.restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact IntermediateField.subset_adjoin E S (Or.inl hz)
  have hω : ∀ ω : Ω, f ω ∈ L := by
    intro ω
    have h1 : f ω ∈ (IntermediateField.adjoin K (s : Set Ω)).map f :=
      (IntermediateField.mem_map _).2 ⟨ω, by rw [hs]; trivial, rfl⟩
    rw [IntermediateField.adjoin_map] at h1
    exact hK h1
  have hP : ∀ p : MvPolynomial (SVars D m) Ω,
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) p ∈ L := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h := hω a
      simpa [f, MvPolynomial.algebraMap_eq] using h
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact L.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact L.mul_mem hp (IntermediateField.subset_adjoin E S (Or.inr ⟨i, rfl⟩))
  have htop : L = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (SVars D m) Ω) z
    exact L.div_mem (hP a) (hP b)
  have hfd : FiniteDimensional E L :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end ReciprocityTheory.MultiplicativeHeights
end

