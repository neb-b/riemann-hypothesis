module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactUnitariesIntegralOrbitOfHankelDetNe
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SuppBdd

theorem isClosed_unitary_set {n : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    [StarRing E] [ContinuousStar E] :
    IsClosed ((Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E))) := by
  have : ((Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E))) =
      {U | star U * U = 1} ∩ {U | U * star U = 1} := by
    ext U; simp [Matrix.unitaryGroup, Unitary.mem_iff]
  rw [this]
  exact (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
    (isClosed_eq (continuous_id.mul continuous_star) continuous_const)

theorem pow_conj {n : ℕ} {E : Type} [CommRing E] [StarRing E] (g : Matrix.unitaryGroup (Fin n) E)
    (A : Matrix (Fin n) (Fin n) E) (j : ℕ) : (g.1 * A * star g.1) ^ j = g.1 * A ^ j * star g.1 := by
  have hg : star g.1 * g.1 = 1 := Unitary.star_mul_self_of_mem g.2
  have hg' : g.1 * star g.1 = 1 := Unitary.mul_star_self_of_mem g.2
  induction j with
  | zero => simp [hg']
  | succ j ih =>
    rw [pow_succ, ih, pow_succ]
    calc g.1 * A ^ j * star g.1 * (g.1 * A * star g.1) = g.1 * A ^ j * (star g.1 * g.1) * A * star g.1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem Bm_actU {n : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g : Matrix.unitaryGroup (Fin n) E) (Y : Hn n F E) :
    Bm (actU g Y).toGl = g.1 * Bm Y.toGl := by
  have hg : star g.1 * g.1 = 1 := Unitary.star_mul_self_of_mem g.2
  ext i j
  have h1 : ((g.1 * Y.1.1 * star g.1) ^ (j : ℕ)) *ᵥ (g.1 *ᵥ Y.2.1) = g.1 *ᵥ ((Y.1.1 ^ (j : ℕ)) *ᵥ Y.2.1) := by
    rw [pow_conj, mulVec_mulVec, mulVec_mulVec]
    congr 1
    rw [Matrix.mul_assoc, hg, Matrix.mul_one]
  have h2 : Bm (actU g Y).toGl i j = (g.1 *ᵥ ((Y.1.1 ^ (j : ℕ)) *ᵥ Y.2.1)) i := by
    rw [← h1]; rfl
  rw [h2, Matrix.mul_apply]
  simp only [mulVec, dotProduct, Bm, Hn.toGl, of_apply]

theorem exists_compact_of_integral : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 →
    ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by
  intro F E _ _ _ _ _ n Y hD
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  set B := Bm Y.toGl with hBdef
  have hB : IsUnit B.det := by
    have h := GlobalTheory.JR.NormalFormL.hankel_eq Y.toGl
    have : (Cm Y.toGl * B).det ≠ 0 := by rw [h]; exact hD
    rw [det_mul] at this
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul this)
  let Φ : Matrix (Fin n) (Fin n) E × (Fin n → E) → Matrix (Fin n) (Fin n) E :=
    fun p => (Matrix.of fun i (j : Fin n) => ((p.1 ^ (j : ℕ)) *ᵥ p.2) i) * B⁻¹
  let S : Set (Matrix (Fin n) (Fin n) E × (Fin n → E)) :=
    {A | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ {v | ∀ i, ‖v i‖ ≤ 1}
  have hS : IsCompact S := by
    apply IsCompact.prod
    · have : {A : Matrix (Fin n) (Fin n) E | ∀ i j, ‖A i j‖ ≤ 1} =
          Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : E) 1) := by
        ext A; simp only [Set.mem_setOf_eq]
        exact ⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i trivial j trivial⟩
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    · have : {v : Fin n → E | ∀ i, ‖v i‖ ≤ 1} = Set.pi Set.univ (fun _ => Metric.closedBall (0 : E) 1) := by
        ext v; simp
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hΦ : Continuous Φ := by
    refine Continuous.matrix_mul ?_ continuous_const
    refine continuous_matrix fun i j => ?_
    exact (continuous_apply i).comp ((continuous_fst.pow (j : ℕ)).matrix_mulVec continuous_snd)
  refine ⟨Subtype.val ⁻¹' (Φ '' S), ?_, ?_⟩
  · exact (isClosed_unitary_set (n := n) (E := E)).isClosedEmbedding_subtypeVal.isCompact_preimage (hS.image hΦ)
  · intro g hg
    have hm := Set.mem_of_indicator_ne_zero hg
    refine ⟨((actU g Y).1.1, (actU g Y).2.1), ⟨hm.1, hm.2.1⟩, ?_⟩
    show Bm (actU g Y).toGl * B⁻¹ = g.1
    rw [Bm_actU, ← hBdef, Matrix.mul_nonsing_inv_cancel_right _ _ hB]

end GlobalTheory.JR.SuppBdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldFiniteOverCdv
section
open NumberField Formalism.L2.Pj

namespace GlobalTheory.ComplexEmbedding

open Cardinal IsLocalRing

theorem exists_digits_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (ϖ : V) (hϖ : Irreducible ϖ) (s : ResidueField V → V) (hs : ∀ r, residue V (s r) = r) :
    ∀ (n : ℕ) (x : V), ∃ f : Fin n → ResidueField V,
      x - ∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) ∈ maximalIdeal V ^ n := by
  intro n
  induction n with
  | zero => intro x; exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨f, hf⟩ := ih x
    have hm : maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    have hf' := hf
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hf'
    obtain ⟨y, hy⟩ := hf'
    refine ⟨Fin.snoc f (residue V y), ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
    have hxy : x - (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) + s (residue V y) * ϖ ^ n) =
        ϖ ^ n * (y - s (residue V y)) := by
      rw [← sub_sub, hy]; ring
    rw [hxy, pow_succ]
    have hϖm : ϖ ∈ maximalIdeal V := (mem_maximalIdeal _).2 hϖ.not_isUnit
    have hym : y - s (residue V y) ∈ maximalIdeal V := by
      rw [← residue_eq_zero_iff, map_sub, hs, sub_self]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖm n) hym

theorem countable_quotient_pow_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Countable (ResidueField V)] (n : ℕ) : Countable (V ⧸ maximalIdeal V ^ n) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let s : ResidueField V → V := Function.surjInv (residue_surjective (R := V))
  have hs : ∀ r, residue V (s r) = r := Function.surjInv_eq _
  have hsurj : Function.Surjective (fun f : Fin n → ResidueField V =>
      Ideal.Quotient.mk (maximalIdeal V ^ n) (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ))) := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨f, hf⟩ := exists_digits_of_dvr V ϖ hϖ s hs n x
    exact ⟨f, (Ideal.Quotient.eq.2 hf).symm⟩
  exact hsurj.countable

theorem mk_le_continuum_of_countable_residueField (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Countable (ResidueField V)] : #V ≤ 𝔠 := by
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    haveI := countable_quotient_pow_of_dvr V n; mk_le_aleph0).trans ?_
  simp

theorem exists_embedding_fractionField_of_finite :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V),
      Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) →
      ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by
  intro K _ _ σ T T' g _ hfin hc io
  have hV : #T.V ≤ 𝔠 := mk_le_continuum_of_countable_residueField T.V
  letI : Algebra T.V T'.V := g.toAlgebra
  haveI : Module.Finite T.V T'.V := hfin
  obtain ⟨d, φ, hφ⟩ := Module.Finite.exists_fin' T.V T'.V
  have hV' : #T'.V ≤ 𝔠 := by
    refine (mk_le_of_surjective hφ).trans ?_
    rw [mk_arrow, mk_fin, lift_id, lift_natCast]
    refine (power_le_power_right hV).trans ?_
    exact power_nat_le aleph0_le_continuum
  have hF : #T'.Fr ≤ 𝔠 := by
    rw [show #T'.Fr = #T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]
    exact hV'
  exact @exists_embedding_of_mk_le_continuum K T'.Fr _ _ _ io.toAlgebra hF σ

end GlobalTheory.ComplexEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedBasis
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.GaloisDescentLattice

theorem sigma_smul {K : UQ} (B : InvAlg K) {a b : K.O}
    (hab : K.c (algebraMap K.O K.E a) = algebraMap K.O K.E b) (y : B.A) :
    B.σ (a • y) = b • B.σ y := by
  rw [← algebraMap_smul K.E a y, ← algebraMap_smul K.E b (B.σ y), Algebra.smul_def, Algebra.smul_def,
    map_mul, B.σ_alg, hab]

theorem exists_fixed_basis : ∀ (K : UQ) (B : InvAlg K) (M : Submodule K.O B.A), IsLat K.O K.E M →
    (∀ y ∈ M, B.σ y ∈ M) → ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A,
      Submodule.span K.O (Set.range e) = M ∧ ∀ i, B.σ (e i) = e i := by
  intro K B M hM hσ
  obtain ⟨d, d', hdd', hunit⟩ := K.c_res
  have hd'd : K.c (algebraMap K.O K.E d') = algebraMap K.O K.E d := by rw [← hdd', K.c_c]
  obtain ⟨u, hu⟩ := (IsLocalRing.notMem_maximalIdeal.mp hunit).exists_left_inv

  let S : Type := {y : B.A // y ∈ M ∧ B.σ y = y}
  let v : S → M := fun s => ⟨s.1, s.2.1⟩
  have hspan : Submodule.span K.O (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : B.σ y ∈ M := hσ y hy
    have h1m : y + B.σ y ∈ M := M.add_mem hy hy'
    have h2m : d • y + d' • B.σ y ∈ M := M.add_mem (M.smul_mem d hy) (M.smul_mem d' hy')
    have h1f : B.σ (y + B.σ y) = y + B.σ y := by rw [map_add (f := _), B.σ_σ, add_comm]
    have h2f : B.σ (d • y + d' • B.σ y) = d • y + d' • B.σ y := by
      rw [map_add (f := _), sigma_smul B hdd', sigma_smul B hd'd, B.σ_σ, add_comm]
    have hmem1 : (⟨y + B.σ y, h1m⟩ : M) ∈ Submodule.span K.O (Set.range v) :=
      Submodule.subset_span ⟨⟨_, h1m, h1f⟩, rfl⟩
    have hmem2 : (⟨d • y + d' • B.σ y, h2m⟩ : M) ∈ Submodule.span K.O (Set.range v) :=
      Submodule.subset_span ⟨⟨_, h2m, h2f⟩, rfl⟩
    have hy_eq : (⟨y, hy⟩ : M) = u • ((⟨d • y + d' • B.σ y, h2m⟩ : M) - d' • (⟨y + B.σ y, h1m⟩ : M)) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_sub, smul_add]
      have : d • y + d' • B.σ y - (d' • y + d' • B.σ y) = (d - d') • y := by rw [sub_smul]; abel
      rw [this, smul_smul, hu, one_smul]
    rw [hy_eq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hmem2 (Submodule.smul_mem _ _ hmem1))

  haveI : Module.Finite K.O M := Module.Finite.iff_fg.mpr hM.1
  haveI : Module.IsTorsionFree K.O M := ⟨fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h0 : algebraMap K.O K.E r ≠ 0 := by
      intro h; exact hr0 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
    change r • x = r • y at hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simp only [Submodule.coe_smul] at this
    rw [← algebraMap_smul K.E r (x : B.A), ← algebraMap_smul K.E r (y : B.A)] at this
    exact smul_right_injective B.A h0 this⟩
  haveI : Module.Free K.O M := Module.free_of_finite_type_torsion_free'
  haveI : Module.FinitePresentation K.O M := Module.finitePresentation_of_finite K.O M
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hspan
  haveI : Finite κ := Module.Finite.finite_basis b
  let w : κ → B.A := fun i => (b i : B.A)
  have hwO : LinearIndependent K.O w :=
    b.linearIndependent.map' M.subtype M.ker_subtype
  have hwE : LinearIndependent K.E w := (LinearIndependent.iff_fractionRing K.O K.E).mp hwO
  have hspanO : Submodule.span K.O (Set.range w) = M := by
    have : Set.range w = M.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanE : ⊤ ≤ Submodule.span K.E (Set.range w) := by
    rw [← hM.2, Submodule.span_le]
    intro x hx
    have : x ∈ Submodule.span K.O (Set.range w) := by rw [hspanO]; exact hx
    exact Submodule.span_le_restrictScalars K.O K.E _ this
  let bE : Module.Basis κ K.E B.A := Module.Basis.mk hwE hspanE
  let e := bE.reindex (bE.indexEquiv (Module.finBasis K.E B.A))
  refine ⟨e, ?_, ?_⟩
  · rw [Module.Basis.range_reindex, Module.Basis.coe_mk]; exact hspanO
  · intro i
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    show B.σ (b _ : B.A) = (b _ : B.A)
    rw [hb]
    exact (a _).2.2

end GlobalTheory.GaloisDescentLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlConjugateLastBasisNormalFormOfNeZero
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem full_blocks {r : ℕ} {k : Type} [CommRing k] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    full (blocks A) = A := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [full, blocks, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castSucc,
      finSumFinEquiv_symm_last]

def nfMat {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k :=
  Matrix.of fun i j => if i = Fin.last r then c j else if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

theorem nfMat_mulVec_castSucc {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k)
    (i : Fin r) : (nfMat c *ᵥ v) (Fin.castSucc i) = v i.succ := by
  simp only [Matrix.mulVec, dotProduct, nfMat, Matrix.of_apply, Fin.castSucc_ne_last, if_false]
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [if_neg]; · simp
    intro h; apply hj; ext; simp [h]
  · simp

theorem nfMat_mulVec_last {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k) :
    (nfMat c *ᵥ v) (Fin.last r) = c ⬝ᵥ v := by
  simp [Matrix.mulVec, dotProduct, nfMat]

theorem nfMat_injective {r : ℕ} {k : Type} [Field k] (c : Fin (r + 1) → k) (h0 : c 0 ≠ 0) :
    Function.Injective (nfMat c).mulVec := by
  intro x y hxy
  set v := x - y with hv
  have key : nfMat c *ᵥ v = 0 := by rw [hv, Matrix.mulVec_sub, hxy, sub_self]
  have hs : ∀ i : Fin r, v i.succ = 0 := fun i => by
    rw [← nfMat_mulVec_castSucc c v i, key]; rfl
  have hl : c ⬝ᵥ v = 0 := by rw [← nfMat_mulVec_last c v, key]; rfl
  have h0v : v 0 = 0 := by
    rw [dotProduct, Fin.sum_univ_succ] at hl
    simp only [hs, mul_zero, Finset.sum_const_zero, add_zero] at hl
    exact (mul_eq_zero.mp hl).resolve_left h0
  have : v = 0 := by
    funext j
    induction j using Fin.cases with
    | zero => exact h0v
    | succ i => exact hs i
  exact sub_eq_zero.mp this

theorem eL_vecMul_nfMat {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    eL r k ᵥ* nfMat c = c := by
  funext j
  simp [eL, Matrix.vecMul, dotProduct, nfMat, Pi.single_apply, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem shiftCompanionLastRowMatrix_mulVec_firstBasis {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    nfMat c *ᵥ (fun i : Fin (r + 1) => if (i : ℕ) = 0 then (1 : k) else 0) = c 0 • eL r k := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [nfMat, Matrix.mulVec, dotProduct, eL]
  | cast i =>
    rw [nfMat_mulVec_castSucc]
    simp [eL, Pi.single_apply, Fin.castSucc_ne_last]

theorem glNormal_of_ne_zero : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 →
    ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  intro k _ r a h0
  have hu : IsUnit (GlobalTheory.JR.Step.nfMat a.2.1) :=
    Matrix.mulVec_injective_iff_isUnit.mp (GlobalTheory.JR.Step.nfMat_injective a.2.1 h0)
  refine ⟨hu.unit, GlobalTheory.JR.Step.blocks ((hu.unit : Matrix _ _ k) * companion a.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix _ _ k)), ?_⟩
  have hg : ((hu.unit : GL (Fin (r + 1)) k) : Matrix _ _ k) = GlobalTheory.JR.Step.nfMat a.2.1 := rfl
  have hinv : GlobalTheory.JR.Step.eL r k ᵥ* (GlobalTheory.JR.Step.nfMat a.2.1) = a.2.1 := GlobalTheory.JR.Step.eL_vecMul_nfMat a.2.1
  unfold act sec GlobalTheory.JR.Step.lift
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact (GlobalTheory.JR.Step.full_blocks _).symm
  · simp only [hg]; exact GlobalTheory.JR.Step.shiftCompanionLastRowMatrix_mulVec_firstBasis a.2.1
  · show a.2.1 ᵥ* _ = _
    have hgi : GlobalTheory.JR.Step.nfMat a.2.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = 1 := by
      exact hu.unit.mul_inv
    have e : (GlobalTheory.JR.Step.eL r k ᵥ* GlobalTheory.JR.Step.nfMat a.2.1) ᵥ*
        ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = GlobalTheory.JR.Step.eL r k := by
      rw [Matrix.vecMul_vecMul, hgi, Matrix.vecMul_one]
    rw [hinv] at e
    exact e

end GlobalTheory.JR.Step
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHyperplaneResidueOutsideTranslates
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem GlobalTheory.gen_type_core : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v) → ∀ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * (Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) * x) = x := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ x hx
  obtain ⟨a, ha, hA⟩ := GlobalTheory.T.exists_residue_annihilator_of_not_standard_column_form_alt O K r t ϖ hϖ x hx
  refine ⟨a, ha, fun g hg L hL => ?_⟩
  set S : Submodule K (Fin r ⊕ Fin t → K) := Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) with hS
  let U : Submodule O (Fin r ⊕ Fin t → O) := Submodule.comap ((Algebra.linearMap O K).compLeft (Fin r ⊕ Fin t)) (S.restrictScalars O)
  have hU : ∀ u, u ∈ U ↔ (fun i => algebraMap O K (u i)) ∈ S := fun u => Iff.rfl
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.residue_top_factor_through_bottom O r t U a (fun u hu h2 => hA u ((hU u).1 hu) h2) (g : Matrix (Fin r) (Fin r) _) hg
  obtain ⟨P, hP1, hP2⟩ := _root_.GlobalTheory.dvr_matrix_proj_preimage O K (Fin r ⊕ Fin t) S
  set bt : Matrix (Fin r) (Fin t) O := b.map (Function.surjInv IsLocalRing.residue_surjective) with hbt
  have hbt' : bt.map (IsLocalRing.residue O) = b := by
    ext i j; simp [hbt, Function.surjInv_eq]
  set q₀ : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O := Matrix.fromBlocks L bt 0 1 with hq₀

  have key : ∀ u ∈ U, ∀ i, IsLocalRing.residue O (Matrix.mulVec (1 - q₀) u i) = 0 := by
    intro u hu i
    have h1 := hb u hu
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, map_sub, sub_eq_zero]
    rw [RingHom.map_mulVec, hq₀, Matrix.fromBlocks_map]
    rw [Matrix.fromBlocks_mulVec]
    rcases i with i | i
    · have := congrFun h1 i
      simp only [Sum.elim_inl, Pi.add_apply] at this ⊢
      rw [hL, hbt']
      simpa [Function.comp_def] using this.symm
    · simp [Function.comp_def]
  have hPx : P * x = x := by
    ext i j
    have := hP2 (fun i => x i j) (Submodule.subset_span ⟨j, rfl⟩)
    exact congrFun this i
  set q := q₀ + (1 - q₀) * P with hq
  have hqx : q * x = x := by
    rw [hq, Matrix.add_mul, Matrix.mul_assoc, hPx, Matrix.sub_mul, Matrix.one_mul]; abel
  have hqq : ∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (q₀ i j) := by
    intro i j
    have hcol : (fun l => P l j) ∈ U := by
      have := hP1 (Pi.single j 1)
      rw [hU]; simpa [Matrix.mulVec_single] using this
    have := key _ hcol i
    rw [hq, Matrix.add_apply, map_add (f := _)]
    have e : ((1 - q₀) * P) i j = Matrix.mulVec (1 - q₀) (fun l => P l j) i := rfl
    rw [e, this, add_zero]
  obtain ⟨h, h1, h2, h3⟩ := _root_.GlobalTheory.gl_factor_fromBlocks_mod_uniformizer O r t ϖ hϖ g L hL bt q hqq
  exact ⟨h, h1, h2, by rw [← Matrix.mul_assoc, h3, hqx]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsZeroTranslationInvariantOfLocallyConst
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem isTest_nhds_inv : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ),
    IsTest f → ∃ U ∈ 𝓝 (0 : X), ∀ x : X, ∀ u ∈ U, f (x + u) = f x := by
  intro X _ _ _ f hf
  obtain ⟨hlc, hcs⟩ := hf
  have hK : IsCompact (tsupport f) := hcs
  have key : ∀ᶠ u in 𝓝 (0 : X), ∀ y ∈ tsupport f, f (y + u) = f y := by
    refine hK.eventually_forall_of_forall_eventually (P := fun u y => f (y + u) = f y) ?_
    intro y _
    have hy : ∀ᶠ z in 𝓝 y, f z = f y := (IsLocallyConstant.iff_eventually_eq f).1 hlc y
    have hc : Filter.Tendsto (fun p : X × X => p.2 + p.1) (𝓝 ((0 : X), y)) (𝓝 y) := by
      have hcont : Continuous fun p : X × X => p.2 + p.1 := continuous_snd.add continuous_fst
      have := hcont.tendsto ((0 : X), y)
      simpa only [add_zero] using this
    have h2 : Filter.Tendsto (fun p : X × X => p.2) (𝓝 ((0 : X), y)) (𝓝 y) :=
      (continuous_snd.tendsto ((0 : X), y))
    filter_upwards [hc.eventually hy, h2.eventually hy] with p hp1 hp2
    exact hp1.trans hp2.symm
  have hneg : Filter.Tendsto (fun u : X => -u) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : X))
  refine ⟨{u | ∀ y ∈ tsupport f, f (y + u) = f y} ∩ (fun u : X => -u) ⁻¹' {u | ∀ y ∈ tsupport f, f (y + u) = f y},
    Filter.inter_mem key (hneg key), ?_⟩
  rintro x u ⟨h1, h2⟩
  by_cases hx : x ∈ tsupport f
  · exact h1 x hx
  by_cases hxu : x + u ∈ tsupport f
  · have := h2 (x + u) hxu
    simp only [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPowerStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → ∀ U : ℕ → Matrix m m F, (∀ i j, ‖(U 0 - 1) i j‖ < 1) → (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) → ∀ b : m → F, Integral b → ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by
  first | exact @GlobalTheory.PMonE.existsUnique_integral_gsum_eq | exact GlobalTheory.PMonE.existsUnique_integral_gsum_eq | (intros; apply GlobalTheory.PMonE.existsUnique_integral_gsum_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlgStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg : ∀ (K : UQ) (B : InvAlg K) (u : B.A), u * B.σ u = 1 → ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  first | exact @GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | exact GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | (intros; apply GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenMulLeftImageLatticeStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 → {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  first | exact @GlobalTheory.UnitLemma.finite_between_mulLat | exact GlobalTheory.UnitLemma.finite_between_mulLat | (intros; apply GlobalTheory.UnitLemma.finite_between_mulLat <;> assumption)
end

