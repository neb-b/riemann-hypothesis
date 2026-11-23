module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import GroundTheory.AutomorphicForms.StableConjCyclic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0051
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmHasse
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.EllipticCentralizerQuotientCompact
section
open PositivityTheory.Rg.Tf.Geo
open NumberField IsDedekindDomain Matrix Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup
open PositivityTheory.Rg.Tf.Core
open scoped NumberField.AdeleRing Pointwise

private def krylovMatrixOfRowVector {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    Matrix (Fin n) (Fin n) R := Matrix.of fun k => x ᵥ* M ^ (k : ℕ)

private theorem vecMul_krylov {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (x c : Fin n → R) :
    c ᵥ* krylovMatrixOfRowVector M x = x ᵥ* ∑ k : Fin n, c k • M ^ (k : ℕ) := by
  rw [Matrix.vecMul_sum, Matrix.vecMul_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.vecMul_smul]
  rfl

private theorem krylov_mul_commute {R : Type*} [CommRing R] {n : ℕ} {M t : Matrix (Fin n) (Fin n) R} (h : Commute M t)
    (x : Fin n → R) : krylovMatrixOfRowVector M x * t = krylovMatrixOfRowVector M (x ᵥ* t) := by
  ext k j
  have : (krylovMatrixOfRowVector M x * t) k j = ((x ᵥ* M ^ (k : ℕ)) ᵥ* t) j := rfl
  rw [this, vecMul_vecMul, (h.pow_left k).eq, ← vecMul_vecMul]
  rfl

private theorem krylov_map_alt {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (x : Fin n → R) : (krylovMatrixOfRowVector M x).map f = krylovMatrixOfRowVector (M.map f) (f ∘ x) := by
  ext k j
  have h : (M.map f) ^ (k : ℕ) = (M ^ (k : ℕ)).map f := by
    simpa using (map_pow f.mapMatrix M k).symm
  change f ((x ᵥ* M ^ (k : ℕ)) j) = ((f ∘ x) ᵥ* (M.map f) ^ (k : ℕ)) j
  rw [h, RingHom.map_vecMul]

private theorem krylov_det_ne_zero {F : Type*} [Field F] {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : Irreducible M.charpoly) {x : Fin n → F} (hx : x ≠ 0) : (krylovMatrixOfRowVector M x).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  rw [vecMul_krylov] at hc0
  set p : F[X] := ∑ k : Fin n, C (c k) * X ^ (k : ℕ) with hp
  have hpa : aeval M p = ∑ k : Fin n, c k • M ^ (k : ℕ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hp, map_sum, Algebra.smul_def]
  have hdeg : p.degree < n := degree_sum_fin_lt c
  have hp0 : p ≠ 0 := by
    intro h
    apply hc
    funext k
    have := congrArg (fun q : F[X] => q.coeff k) h
    simpa [hp, finsetSum_coeff, coeff_X_pow, Fin.val_inj] using this
  have hnd : ¬ M.charpoly ∣ p := by
    intro hd
    have := degree_le_of_dvd hd hp0
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this
    exact absurd hdeg (not_lt.2 this)
  obtain ⟨a, b, hab⟩ := (hM.coprime_iff_not_dvd).2 hnd
  have h1 := congrArg (aeval M) hab
  rw [map_add (f := _), map_mul, Matrix.aeval_self_charpoly, mul_zero, zero_add, mul_comm b p, map_mul, map_one, hpa] at h1
  apply hx
  rw [← vecMul_one x, ← h1, ← vecMul_vecMul, hc0, zero_vecMul]

private theorem commute_of_krylov_unit {R : Type*} [CommRing R] {n : ℕ} {M s t : Matrix (Fin n) (Fin n) R} {x : Fin n → R}
    (hx : IsUnit (krylovMatrixOfRowVector M x)) (hs : Commute M s) (ht : Commute M t) : Commute s t := by
  obtain ⟨u, hu⟩ := hx
  set c : Fin n → R := (x ᵥ* t) ᵥ* (↑u⁻¹ : Matrix (Fin n) (Fin n) R) with hc
  set q : Matrix (Fin n) (Fin n) R := ∑ k : Fin n, c k • M ^ (k : ℕ) with hq
  have h1 : x ᵥ* q = x ᵥ* t := by
    rw [hq, ← vecMul_krylov, hc, ← hu, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hMq : Commute M q :=
    Commute.sum_right _ _ _ fun k _ => ((Commute.refl M).pow_right k).smul_right _
  have h2 : t = q := by
    have : (u : Matrix (Fin n) (Fin n) R) * t = u * q := by
      rw [hu, krylov_mul_commute ht, krylov_mul_commute hMq, h1]
    exact (Units.mul_right_inj u).1 this
  rw [h2]
  exact Commute.sum_right _ _ _ fun k _ => (hs.symm.pow_right k).smul_right _

private theorem adelic_hadamard_inequality {K : Type*} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤
      ∏ i, adelicNorm ((Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  classical
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_adelicBorel_mul_maxCompact g
  have hk1 := mem_normOneGL.1 (maxCompact_le_normOneGL hk)
  have hu := isUnit_apply_self_of_mem_adelicBorel hb
  have hdet : AdelicGLn.det K n b = ∏ i, (hu i).unit := by
    refine Units.ext ?_
    rw [AdelicGLn.coe_det, Matrix.det_of_isUpperTriangular hb, Units.coe_prod]
    rfl
  rw [map_mul, map_mul, Positive.val_mul, hk1, mul_one, hdet, map_prod, coe_finset_prod_pos]
  refine Finset.prod_le_prod₀ (fun i _ => (ideleModule K (hu i).unit).2.le) fun i _ => ?_
  rw [Units.val_mul, ← vecMul_vecMul, adelicNorm_vecMul_maxCompact _ hk, ← adelicNorm_single_units i]
  have he : (Pi.single i (((hu i).unit : IdeleGroup K) : 𝔸[K]) : Fin n → 𝔸[K]) =
      (((hu i).unit : IdeleGroup K) : 𝔸[K]) • (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  have key := adelicNorm_le_of_local ((hasFiniteContent_single_one (K := K) i).smul (hu i).unit)
    ((hasFiniteContent_single_one (K := K) i).vecMul b) (fun _ => 1) (fun _ => 1) ∅ (fun w => ?_)
    (fun _ _ => rfl) (fun v => ?_)
  · rw [he]
    simpa using key
  · rw [one_mul, infComp_smul, euclidNorm_smul]
    have h1 : euclidNorm (infComp w (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K])) = 1 := by
      rw [← euclidNorm_pi_single_one (E := w.Completion) i]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [infComp]
      · simp [infComp, Pi.single_eq_of_ne hj]; rfl
    rw [h1, mul_one, single_one_vecMul]
    exact norm_le_euclidNorm (infComp w ((b : Matrix (Fin n) (Fin n) 𝔸[K]).row i)) i
  · rw [one_mul, finComp_smul, norm_smul]
    have h1 : ‖finComp v (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K])‖ = 1 := by
      rw [← norm_pi_single_one (E := v.adicCompletion K) i]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [finComp] <;> rfl
      · simp [finComp, Pi.single_eq_of_ne hj]; rfl
    rw [h1, mul_one, single_one_vecMul]
    exact norm_le_pi_norm (finComp v ((b : Matrix (Fin n) (Fin n) 𝔸[K]).row i)) i

private theorem centralizer_compact_fundamental {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {γ : G} (hγ : γ ∈ Γ) {D : Set G} (hD : IsCompact D)
    (h : ∀ t : Subgroup.centralizer {γ}, ∃ g ∈ Γ, ∃ y ∈ D, (t : G) = g * y) :
    ∃ C : Set (Subgroup.centralizer {γ}), IsCompact C ∧ ∀ t : Subgroup.centralizer {γ},
      ∃ g : Subgroup.centralizer {γ}, (g : G) ∈ Γ ∧ ∃ y ∈ C, t = g * y := by
  classical
  have hE : IsCompact ((fun y : G => y * γ * y⁻¹) '' D) := hD.image (by fun_prop)
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hfin : ((fun y : G => y * γ * y⁻¹) '' D ∩ (Γ : Set G)).Finite := by
    have h1 : IsCompact (Subtype.val ⁻¹' ((fun y : G => y * γ * y⁻¹) '' D) : Set Γ) :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hE
    refine (h1.finite_of_discrete.image Subtype.val).subset ?_
    rintro z ⟨hz, hzΓ⟩
    exact ⟨⟨z, hzΓ⟩, hz, rfl⟩
  have hr : ∀ δ : G, ∃ r ∈ Γ, (∃ g ∈ Γ, g⁻¹ * γ * g = δ) → r⁻¹ * γ * r = δ := fun δ => by
    by_cases hδ : ∃ g ∈ Γ, g⁻¹ * γ * g = δ
    · obtain ⟨g, hg, hg'⟩ := hδ
      exact ⟨g, hg, fun _ => hg'⟩
    · exact ⟨1, one_mem _, fun h => absurd h hδ⟩
  choose r hrΓ hr using hr
  have hC : IsCompact (⋃ δ ∈ (fun y : G => y * γ * y⁻¹) '' D ∩ (Γ : Set G), (fun y => r δ * y) '' D) :=
    hfin.isCompact_biUnion fun δ _ => hD.image (by fun_prop)
  have hZ : IsClosed ((Subgroup.centralizer {γ} : Subgroup G) : Set G) := by
    have : ((Subgroup.centralizer {γ} : Subgroup G) : Set G) = {x | x * γ = γ * x} := by
      ext x
      exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  refine ⟨Subtype.val ⁻¹' _, hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hC, fun t => ?_⟩
  obtain ⟨g, hg, y, hy, hty⟩ := h t
  have ht : (t : G) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
  have hδ : g⁻¹ * γ * g = y * γ * y⁻¹ := by
    rw [hty] at ht
    calc g⁻¹ * γ * g = g⁻¹ * (γ * (g * y)) * y⁻¹ := by group
      _ = y * γ * y⁻¹ := by rw [← ht]; group
  have hr1 := hr _ ⟨g, hg, hδ⟩
  set ρ := r (y * γ * y⁻¹) with hρ
  have hz : g * ρ⁻¹ ∈ Subgroup.centralizer {γ} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * ρ⁻¹ * γ = g * (ρ⁻¹ * γ * ρ) * ρ⁻¹ := by group
      _ = γ * (g * ρ⁻¹) := by rw [hr1, ← hδ]; group
  refine ⟨⟨_, hz⟩, mul_mem hg (inv_mem (hrΓ _)), (⟨_, hz⟩ : Subgroup.centralizer {γ})⁻¹ * t, ?_, by group⟩
  refine Set.mem_biUnion (x := y * γ * y⁻¹) ⟨⟨y, hy, rfl⟩, ?_⟩ ⟨y, hy, ?_⟩
  · rw [← hδ]
    exact mul_mem (mul_mem (inv_mem hg) hγ) hg
  · change ρ * y = (g * ρ⁻¹)⁻¹ * (t : G)
    rw [hty]; group

theorem UpperTheory.ConvolutionTheory.G.elliptic_centralizer_quotient_compact :
    N4 := by
  intro F _ _ n γ γ₁ hγ hirr
  set M : Matrix (Fin n) (Fin n) 𝔸[F] := Units.val (AdelicGLn.diagonal F n γ) with hM
  have hcom : ∀ t : Subgroup.centralizer {γ₁},
      Commute M (((t : G1 F n) : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F]) := fun t => by
    have ht : (t : G1 F n) * γ₁ = γ₁ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
    have := congrArg (fun z : G1 F n => ((z : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F])) ht
    simp only [Subgroup.coe_mul, Units.val_mul, hγ] at this
    exact this.symm
  have hK : ∀ x : Fin n → F, x ≠ 0 → ∃ κ : GL (Fin n) F,
      ((AdelicGLn.diagonal F n κ : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F]) =
        krylovMatrixOfRowVector M (ratVec x) := fun x hx =>
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (krylov_det_ne_zero hirr hx),
      krylov_map_alt (algebraMap F 𝔸[F]) _ x⟩
  have hn : 0 < n := by
    have := hirr.natDegree_pos
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  constructor
  · intro s t
    obtain ⟨κ, hκ⟩ := hK (Pi.single ⟨0, hn⟩ 1) (by simp)
    have := commute_of_krylov_unit (hκ ▸ Units.isUnit _) (hcom s) (hcom t)
    exact Subtype.ext (Subtype.ext (Units.ext this.eq))
  obtain ⟨P, hP, hPle⟩ := exists_adelicNorm_vecMul_le_mul
    (Set.finite_range fun k : Fin n => AdelicGLn.diagonal F n γ ^ (k : ℕ)).isCompact
  obtain ⟨D, hD, hD'⟩ := exists_isCompact_forall_of_pos_le_height (K := F) (n := n) (inv_pos.2 hP)
  refine centralizer_compact_fundamental (Gam F n) (show (γ₁ : AdelicGLn.AdelicGL F n) ∈ AdelicGLn.rationalGL F n from ⟨γ, hγ.symm⟩)
    (isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hD) fun t => ?_
  set τ : AdelicGLn.AdelicGL F n := ((t : G1 F n) : AdelicGLn.AdelicGL F n) with hτ
  have hτ1 : τ ∈ normOneGL (K := F) (n := n) := (t : G1 F n).2
  have hht : ∀ x : Fin n → F, x ≠ 0 → P⁻¹ ≤ height τ x := fun x hx => by
    obtain ⟨κ, hκ⟩ := hK x hx
    have h1 := adelic_hadamard_inequality (AdelicGLn.diagonal F n κ * τ)
    rw [mem_normOneGL.1 (mul_mem (rationalGL_le_normOneGL ⟨κ, rfl⟩) hτ1), Units.val_mul, hκ,
      krylov_mul_commute (hcom t)] at h1
    have h2 : ∏ i : Fin n, adelicNorm ((Pi.single i (1 : 𝔸[F]) : Fin n → 𝔸[F]) ᵥ*
        krylovMatrixOfRowVector M (ratVec x ᵥ* (τ : Matrix (Fin n) (Fin n) 𝔸[F]))) ≤ ∏ _i : Fin n, P * height τ x := by
      refine Finset.prod_le_prod₀ (fun _ _ => adelicNorm_nonneg _) fun i _ => ?_
      have := hPle _ ⟨i, rfl⟩ _ (hasFiniteContent_height τ hx)
      rw [single_one_vecMul]
      rw [Units.val_pow_eq_pow_val] at this
      exact this
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : 1 ≤ P * height τ x :=
      (one_le_pow_iff_of_nonneg (mul_nonneg hP.le (height_nonneg _ _)) hn.ne').1 (h1.trans h2)
    rw [inv_le_iff_one_le_mul₀' hP]
    exact h3
  obtain ⟨g, hg, y, hy, hgy⟩ := hD' τ hτ1 hht
  have hg1 : g ∈ normOneGL (K := F) (n := n) := rationalGL_le_normOneGL hg
  have hy1 : y ∈ normOneGL (K := F) (n := n) := by
    have : y = g⁻¹ * τ := by rw [← hgy, inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem hg1) hτ1
  exact ⟨⟨g, hg1⟩, hg, ⟨y, hy1⟩, hy, Subtype.ext hgy.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.ExistsKrylovDetNeZero
section
open PositivityTheory.Rg.Tf.Geo

private theorem exists_krylov_det_ne_zero {k : Type*} [Field k] [Infinite k] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) (h : M.charpoly.Separable) :
    ∃ v : Fin n → k, (GroundTheory.Automorphic.krylov M v).det ≠ 0 := by
  have hs : (Matrix.toLin' M).charpoly.Separable := by rwa [Matrix.charpoly_toLin']
  obtain ⟨w, hw⟩ := GroundTheory.Automorphic.exists_linearIndependent_pow_apply _ hs
  rw [Module.finrank_fin_fun] at hw
  refine ⟨w, ?_⟩
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit]
  have hcol : (GroundTheory.Automorphic.krylov M w).col =
      fun j : Fin n => (Matrix.toLin' M ^ (j : ℕ)) w := by
    ext1 j
    rw [GroundTheory.Automorphic.krylov_col, ← Matrix.toLin'_pow, Matrix.toLin'_apply]
  rw [hcol]
  exact hw

private theorem isClosed_charpoly_eq {k : Type*} [NontriviallyNormedField k] [Infinite k] {n : ℕ}
    (P : Polynomial k) : IsClosed {g : GL (Fin n) k | (g : Matrix (Fin n) (Fin n) k).charpoly = P} := by
  have : {g : GL (Fin n) k | (g : Matrix (Fin n) (Fin n) k).charpoly = P} =
      ⋂ a : k, {g : GL (Fin n) k | (Matrix.scalar (Fin n) a - (g : Matrix (Fin n) (Fin n) k)).det = P.eval a} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro rfl a
      rw [Matrix.eval_charpoly]
    · intro h
      apply Polynomial.funext
      intro a
      rw [Matrix.eval_charpoly]
      exact h a
  rw [this]
  refine isClosed_iInter fun a => isClosed_eq ?_ continuous_const
  exact (continuous_const.sub Units.continuous_val).matrix_det

private theorem continuous_krylov {k : Type*} [NontriviallyNormedField k] {n : ℕ} (v : Fin n → k) :
    Continuous fun g : GL (Fin n) k => GroundTheory.Automorphic.krylov (g : Matrix (Fin n) (Fin n) k) v := by
  refine continuous_matrix fun i j => ?_
  simp only [GroundTheory.Automorphic.krylov, Matrix.of_apply]
  exact (continuous_apply i).comp (((Units.continuous_val.pow _)).matrix_mulVec continuous_const)

theorem UpperTheory.ConvolutionTheory.G.p1_holds :
    P1 :=
  _root_.UpperTheory.Reformulated.B.ProjectiveLineOf.p1_holds
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.GinvHWCellLastMulMulVecBvecEI
section
open PositivityTheory.Rg.Tf.Geo

noncomputable section

open NumberField IsDedekindDomain Polynomial PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.D
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.G

private theorem map_twNorm {n : ℕ} {k R B : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing B]
    (p : B →+* R) (s : B →+* B) (τ : R ≃ₐ[k] R) (h : ∀ b, p (s b) = τ (p b)) (q : ℕ) (δ : GL (Fin n) B) :
    mapGL n p (twNorm (mapGL n s) q δ) = nm τ q (mapGL n p δ) := by
  unfold twNorm nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  clear hi
  simp only [Function.comp_apply]
  induction i with
  | zero =>
    ext a b
    rfl
  | succ i ih =>
    refine (congrArg (mapGL n p) (pow_succ_apply' (G := GL (Fin n) B) (mapGL n s) i δ)).trans ?_
    ext a b
    have := congrArg (fun g : GL (Fin n) R => τ ((g : Matrix (Fin n) (Fin n) R) a b)) ih
    refine (h _).trans (this.trans ?_)
    rw [pow_succ']
    rfl

private theorem transport {n : ℕ} {F E A B k : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] [CommRing k] [Algebra F k]
    (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (ι : A →+* B) (hι : ∀ a, e (1 ⊗ₜ a) = ι a) (φ : A →ₐ[F] k)
    (γ : GL (Fin n) F) (q : ℕ) (δ : GL (Fin n) B)
    (hδ : twNorm (mapGL n (galOf e σ)) q δ = mapGL n ι (mapGL n (algebraMap F A) γ)) :
    ∃ d, cp (nm (ext k σ) q (n := n) d) = (cp γ).map ((inc k).comp (algebraMap F E)) := by
  let ψ : E ⊗[F] A →ₐ[F] k ⊗[F] E :=
    (Algebra.TensorProduct.comm F E k).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id F E) φ)
  have hψ : ∀ x a, ψ (x ⊗ₜ a) = φ a ⊗ₜ x := fun x a => by simp [ψ]
  let p : B →+* k ⊗[F] E := (ψ : E ⊗[F] A →+* k ⊗[F] E).comp (e.symm : B →+* E ⊗[F] A)
  have hp : ∀ z, p (e z) = ψ z := fun z => by simp [p]
  have h1 : ∀ b, p (galOf e σ b) = ext k σ (p b) := by
    intro b
    obtain ⟨z, rfl⟩ := e.surjective b
    have : galOf e σ (e z) = e (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) z) := by
      simp [galOf]
    rw [this, hp, hp]
    clear this
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x a => simp [hψ, D.ext]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine ⟨mapGL n p δ, ?_⟩
  rw [← map_twNorm p _ _ h1, hδ, cp, cp, ← Matrix.charpoly_map]
  congr 1
  ext a b
  change p (ι (algebraMap F A _)) = inc k (algebraMap F E _)
  rw [← hι, hp, hψ, φ.commutes]
  change _ = (1 : k) ⊗ₜ[F] algebraMap F E _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.ginvH_wCell_last_mul_mulVec_bvec_eI :
    GlobalTheory.Published.HasseNorm → H1 := by
  intro _ F E _ _ _ _ _ _ σ hσ n _ _ γ hγ hinf hfin
  obtain ⟨a, ha, -⟩ := nmHasse F E σ hσ n γ hγ.separable (fun v => by
    obtain ⟨δ, hδ⟩ := hfin v
    refine transport (tensorEquiv' E v) σ (incFin E v) (fun a => ?_) (AlgHom.id F _) γ _ δ (hδ.trans ?_)
    · rw [tensorEquiv'_tmul, map_one, one_mul]
      rfl
    · congr 1) (fun v => by
    obtain ⟨δ, hδ⟩ := hinf
    refine transport (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)) σ
      (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (fun a => ?_)
      (Pi.evalAlgHom F (fun v : InfinitePlace F => v.Completion) v) γ _ δ (hδ.trans ?_)
    · rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
    · congr 1)
  refine ⟨a, Eq.trans ?_ ha⟩
  exact map_twNorm (RingHom.id E) (σ : E →+* E) σ (fun _ => rfl) _ a
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.MonicPolynomialIsMatrixCharpoly
section
open PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Loc Polynomial

private theorem exists_matrix_charpoly {k : Type} [Field k] (P : k[X]) (hP : P.Monic) (n : ℕ)
    (hn : P.natDegree = n) : ∃ M : Matrix (Fin n) (Fin n) k, M.charpoly = P := by
  subst hn
  have hP0 : P ≠ 0 := hP.ne_zero
  have hdim : (AdjoinRoot.powerBasis hP0).dim = P.natDegree := AdjoinRoot.powerBasis_dim hP0
  refine ⟨Matrix.reindex (finCongr hdim) (finCongr hdim)
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasis hP0).basis (AdjoinRoot.powerBasis hP0).gen), ?_⟩
  rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen hP0]
  simp [hP.leadingCoeff]

theorem UpperTheory.ConvolutionTheory.G.monic_polynomial_is_matrix_charpoly :
    N1 := by
  intro k E _ _ _ _ _ _ σ hgen n δ hreg
  obtain ⟨P, hP⟩ := charpoly_normGL_lifts σ hgen δ
  have hPm : P.Monic := Polynomial.monic_of_injective (algebraMap k E).injective
    (by rw [hP]; exact Matrix.charpoly_monic _)
  have hdeg : P.natDegree = n := by
    rw [← Polynomial.natDegree_map (f := algebraMap k E), hP, Matrix.charpoly_natDegree_eq_dim]
    simp
  obtain ⟨M, hM⟩ := exists_matrix_charpoly P hPm n hdeg
  have hMc : (M.map (algebraMap k E)).charpoly = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly := by
    rw [Matrix.charpoly_map, hM, hP]
  have hdetE : (M.map (algebraMap k E)).det = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, hMc]
  have hNu : IsUnit ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (normGL σ δ).isUnit
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [← hdetE] at hNu
    have e : (M.map (algebraMap k E)).det = algebraMap k E M.det := ((algebraMap k E).map_det M).symm
    rw [e, h0, map_zero] at hNu
    exact not_isUnit_zero hNu
  let γ : GL (Fin n) k := Matrix.nonsingInvUnit M hdet
  have hγ : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = M.map (algebraMap k E) := rfl
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep E E n _ hreg).1 ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
    (by rw [hγ]; exact hMc)
  have hx' : normGL σ δ * x = x * incl γ := Units.ext hx
  refine ⟨x, γ, ?_⟩
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have h := twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ x δ
  change twNorm (sigmaGL σ) (Module.finrank k E) (twConj (sigmaGL σ) x δ) = incl γ
  rw [h]
  change x⁻¹ * normGL σ δ * x = incl γ
  rw [mul_assoc, hx', inv_mul_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.NormMapAndSeparableConjugacy
section
open PositivityTheory.Rg.Tf.Geo

open PositivityTheory.Rg.Tf.Loc in
private theorem nm_eq_normGL {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (n q : ℕ)
    (d : GL (Fin n) E) : UpperTheory.ConvolutionTheory.D.nm σ q d = twNorm (sigmaGL σ) q d := by
  unfold UpperTheory.ConvolutionTheory.D.nm twNorm
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [← sigmaGL_pow]
  rfl

open PositivityTheory.Rg.Tf.Loc in
theorem UpperTheory.ConvolutionTheory.G.nm_agrees_with_twisted_norm_sigmaGL :
    N2 := by
  intro k E _ _ _ _ _ _ σ hσ n
  refine ⟨?_, ?_⟩
  · intro δ δ' γ hγ h1 h2
    have hg := UpperTheory.ConvolutionTheory.D.galField k E σ hσ
    have e : ∀ d : GL (Fin n) E, UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) d = normGL σ d :=
      fun d => nm_eq_normGL σ n _ d
    have hsep : (UpperTheory.ConvolutionTheory.D.cp (UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) δ)).Separable := by
      rw [e, h1]
      have hm : UpperTheory.ConvolutionTheory.D.cp (incl γ : GL (Fin n) E) =
          ((γ : Matrix (Fin n) (Fin n) k).charpoly).map (algebraMap k E) := by
        rw [← Matrix.charpoly_map]
        rfl
      rw [hm]
      exact hγ.map
    obtain ⟨x, hx⟩ := UpperTheory.ConvolutionTheory.D.nmInj k E σ _ hg n δ δ' hsep (by rw [e, e, h1, h2])
    exact ⟨x, hx⟩
  · intro γ γ' hγ hc
    obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep k k n (γ : Matrix (Fin n) (Fin n) k) hγ).1 γ' hc.symm
    have hx' : γ * x = x * γ' := Units.ext hx
    refine ⟨x, ?_⟩
    rw [mul_assoc, hx', inv_mul_cancel_left]
end

