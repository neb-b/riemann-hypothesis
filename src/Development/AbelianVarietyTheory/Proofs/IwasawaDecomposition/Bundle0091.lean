module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
public import ReciprocityTheory.Automorphisms.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharCompMemComplexIrrCharSetStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrChar_comp_mem_complexIrrCharSet : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] [inst_3 : CharZero K] (σ : K →+* ℂ) (χ : G → K), IsAbsIrrChar χ → (fun g => σ (χ g)) ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ := by
  first | exact @GlobalTheory.absIrrChar_comp_mem_gxIrrSet | exact GlobalTheory.absIrrChar_comp_mem_gxIrrSet | (intros; apply GlobalTheory.absIrrChar_comp_mem_gxIrrSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.InfTypeLocal

theorem denseRange_atInf (L : Type) [Field L] [NumberField L] :
    DenseRange (fun (k : Lˣ) (w : InfinitePlace L) => atInf w k) := by
  have hg : Topology.IsOpenEmbedding
      (Pi.map (fun (w : InfinitePlace L) => (Units.val : (w.Completion)ˣ → w.Completion))) :=
    Topology.IsOpenEmbedding.piMap (fun w => Units.isOpenEmbedding_val)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap L).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
    have h1 := congrFun hk w
    rw [map_zero] at h1
    exact (v w).ne_zero h1
  refine ⟨v, hv, Units.mk0 k hk0, ?_⟩
  funext w
  exact Units.ext (congrFun hk w).symm

theorem continuous_infIdele (L : Type) [Field L] [NumberField L] (w : InfinitePlace L) :
    Continuous (infIdele L w) := by
  classical
  refine Continuous.units_map _ ?_
  exact Continuous.prodMk (continuous_mulSingle w) continuous_const

theorem exists_ext {L : Type} [Field L] (φ : L →+* ℂ) :
    ∃ e : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous e ∧
      ∀ k : L, e (algebraMap L _ k) = φ k := by
  have h0 : ∀ k : L, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ) (algebraMap L _ k) =
      (InfinitePlace.mk φ).embedding k := fun k => by
    rw [InfinitePlace.Completion.algebraMap_apply]
    simpa using InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ k)
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨_, hc, fun k => by rw [h0, h]⟩
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp hc, fun k => ?_⟩
    rw [RingHom.comp_apply, h0, h]
    simp


open Classical in
theorem infType_iff_local : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ n : I → ℤ, ((∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ↔ ∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) := by
  intro L _ _ I _ φ hφ ψ hψ n
  have hd : ∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) := by
    intro k
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]
    rfl
  constructor
  · intro h
    choose e hec he using fun i => exists_ext (φ i)
    have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => ∏ w, ((ψ (infIdele L w (u w)) : ℂˣ) : ℂ)) =
        fun u => ∏ i, (e i (u (InfinitePlace.mk (φ i))) / ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ)) ^ n i := by
      refine (denseRange_atInf L).equalizer ?_ ?_ ?_
      · refine continuous_finsetProd _ fun w _ => ?_
        exact Units.continuous_val.comp (hψ.comp ((continuous_infIdele L w).comp (continuous_apply w)))
      · refine continuous_finsetProd _ fun i _ => ?_
        have h1 : Continuous fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => e i (u (InfinitePlace.mk (φ i))) :=
          (hec i).comp (Units.continuous_val.comp (continuous_apply _))
        have h2 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, e i (u (InfinitePlace.mk (φ i))) ≠ 0 := fun u =>
          (map_ne_zero _).2 (Units.ne_zero (u (InfinitePlace.mk (φ i))))
        have h3 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ) ≠ 0 := fun u => by
          exact_mod_cast norm_ne_zero_iff.2 (h2 u)
        exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _ fun u => Or.inl (div_ne_zero (h2 u) (h3 u))
      · funext k
        show ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) =
          ∏ i, (e i (algebraMap L _ (k : L)) / ((‖e i (algebraMap L _ (k : L))‖ : ℝ) : ℂ)) ^ n i
        rw [← hd, h]
        simp only [he]
    intro i k
    have h1 := congrFun key (Pi.mulSingle (InfinitePlace.mk (φ i)) (atInf _ k))
    beta_reduce at h1
    rw [Finset.prod_eq_single (InfinitePlace.mk (φ i)), Finset.prod_eq_single i] at h1
    · rw [Pi.mulSingle_eq_same] at h1
      rw [h1, ← he i k]
      rfl
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne (fun hh => hj (hφ.1 hh))]
      simp
    · simp
    · intro w _ hw
      rw [Pi.mulSingle_eq_of_ne hw]
      simp
    · simp
  · intro h k
    rw [hd, ← hφ.prod_comp]
    exact Finset.prod_congr rfl fun i _ => h i k

end GlobalTheory.InfTypeLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharactersPrescribedValues
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BaseChars

theorem eq_of_pow_eq {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {om : (ZMod p)ˣ →* Kˣ} (hom : Function.Injective om)
    {a b : ℕ} (ha : a < p - 1) (hb : b < p - 1) (h : ∀ x, om x ^ a = om x ^ b) : a = b := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h1 := h g
  rw [← map_pow, ← map_pow] at h1
  exact pow_injOn_Iio_orderOf (x := g) (by rwa [Set.mem_Iio, hog]) (by rwa [Set.mem_Iio, hog]) (hom h1)

theorem nonempty_equiv_zmod {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hw : Ideal.absNorm w.asIdeal = p) : Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod p) := by
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  exact ⟨(ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])).symm⟩

end GlobalTheory.BaseChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalMatrixApproximationModIntegral
section
noncomputable section

namespace GlobalTheory.GlobApx

open Formalism.MainNotions.G

theorem mulVec_mem_colSpan {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (w : Fin k → R) :
    g.mulVec (fun j => algebraMap R K (w j)) ∈ colSpan R g := by
  have : g.mulVec (fun j => algebraMap R K (w j)) = ∑ j, w j • fun i => g i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_pow_smul_ge {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ a : ℕ, ∀ N, a ≤ N → ∃ g0 : Matrix (Fin k) (Fin k) R,
      algebraMap R K π ^ N • g = g0.map (algebraMap R K) := by
  obtain ⟨a, g0, h⟩ := GlobalTheory.GO.TupApx.exists_pow_smul (K := K) hπ g
  refine ⟨a, fun N hN => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨π ^ d • g0, ?_⟩
  rw [pow_add, mul_comm, mul_smul, h]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow]

theorem exists_glob_approx : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)] [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)] {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q), (∀ q, Irreducible (π q)) → ∀ (t : F), (∀ q, f q t = algebraMap (W q) (Q q) (π q)) → (∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z)) → ∀ {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)), (∀ q, IsUnit (g q).det) → ∀ (q0 : ι), ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧ B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧ ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) := by
  intro ι _ _ W Q _ _ _ _ _ _ F _ f π hπ t ht hd n g hg q0
  have hp0 : ∀ q, algebraMap (W q) (Q q) (π q) ≠ 0 := fun q =>
    (map_ne_zero_iff _ (IsFractionRing.injective (W q) (Q q))).2 (hπ q).ne_zero
  choose a ha using fun q => exists_pow_smul_ge (hπ q) (g q)
  choose b hb using fun q => exists_pow_smul_ge (hπ q) (g q)⁻¹
  set M := Finset.univ.sup (fun q => a q + b q) with hMdef
  have hM : ∀ q, a q ≤ M ∧ b q ≤ M := fun q => by
    have := Finset.le_sup (f := fun q => a q + b q) (Finset.mem_univ q)
    constructor <;> omega
  choose G hG using fun q => ha q M (hM q).1
  choose H hH using fun q => hb q M (hM q).2
  choose x hx using fun i j => hd (Pi.single (M := W) q0 (G q0 i j)) (2 * M + 1)
  choose z hz using hx
  have hB : ∀ q i j, f q ((t ^ M)⁻¹ * x i j) = (algebraMap (W q) (Q q) (π q) ^ M)⁻¹ *
      (algebraMap (W q) (Q q) (Pi.single (M := W) q0 (G q0 i j) q) +
        algebraMap (W q) (Q q) (π q) ^ (2 * M + 1) * algebraMap (W q) (Q q) (z i j q)) := by
    intro q i j
    rw [map_mul, map_inv₀, map_pow, ht, hz, map_add (f := _), map_mul, map_pow]
  refine ⟨Matrix.of fun i j => (t ^ M)⁻¹ * x i j, 1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0), ?_, ?_, ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hr : IsLocalRing.residue (W q0) (π q0) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]; exact (hπ q0).not_isUnit
    have : (IsLocalRing.residue (W q0)).mapMatrix (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 1 := by
      rw [map_add (f := _), map_one]
      have : (IsLocalRing.residue (W q0)).mapMatrix (π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 0 := by
        ext i j; simp [hr]
      rw [this, add_zero]
    rw [this]; simp
  · have e1 : (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)).map (algebraMap (W q0) (Q q0)) =
        1 + algebraMap (W q0) (Q q0) (π q0) • ((H q0).map (algebraMap (W q0) (Q q0)) *
          (Matrix.of fun i j => z i j q0).map (algebraMap (W q0) (Q q0))) := by
      rw [← Matrix.map_mul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
        Matrix.one_apply, apply_ite (algebraMap (W q0) (Q q0)), map_one, map_zero]
    rw [e1, ← hH q0, mul_add, mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (hg q0), Matrix.one_mul]
    ext i j
    have h2 := congrFun (congrFun (hG q0) i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h2
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hB, Pi.single_eq_same, ← h2]
    have := hp0 q0
    field_simp
    ring
  · intro q hq c
    set zc : Fin n → W q := fun i => z i c q
    have hv : (fun i => f q ((Matrix.of fun i j => (t ^ M)⁻¹ * x i j) i c)) =
        (g q).mulVec (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) := by
      have e2 : (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) =
          algebraMap (W q) (Q q) (π q) • ((H q).map (algebraMap (W q) (Q q))).mulVec
            (fun j => algebraMap (W q) (Q q) (zc j)) := by
        funext j
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e2, ← hH q, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hg q), Matrix.one_mulVec]
      funext i
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [hB, Pi.single_eq_of_ne hq, map_zero, zero_add]
      have := hp0 q
      field_simp
      ring
    rw [hv]
    exact mulVec_mem_colSpan _ _

end GlobalTheory.GlobApx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveCharacterOfIsCyclic
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem (L : Type*) [Field L] [NumberField L] {p : ℕ}
    (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQm, hQ⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)})
      (by
        intro x hx
        rw [RingHom.mem_ker, (algebraMap ℤ (𝓞 L)).injective_int.eq_iff' (map_zero _)] at hx
        simp [hx])
  have hmem : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [hQ]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQm.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : (p : ℤ) ∈ (⊥ : Ideal (𝓞 L)).comap (algebraMap ℤ (𝓞 L)) := by simpa using hmem
  rw [Ideal.mem_comap, Ideal.mem_bot] at this
  exact hp.ne_zero (by simpa using this)

open NumberField IsDedekindDomain in
private theorem exists_injective_units_zmod_hom_units_complex (p : ℕ) [Fact p.Prime] :
    ∃ f : (ZMod p)ˣ →* ℂˣ, Function.Injective f := by
  set n := Nat.card (ZMod p)ˣ
  have hn : NeZero n := ⟨Nat.card_pos.ne'⟩
  have hc : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity n ℂ) := by
    rw [Complex.card_rootsOfUnity]
  exact ⟨(rootsOfUnity n ℂ).subtype.comp (mulEquivOfCyclicCardEq hc).toMonoidHom,
    Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩


open NumberField IsDedekindDomain in
open Classical in
theorem _root_.GlobalTheory.nonempty_piBar_and_omg :
    ∀ (R : _root_.Formalism.BasicNotions.Ranks) (H : _root_.Formalism.BasicNotions.Host R), Nonempty (_root_.Formalism.L2.Host.PiBar H) ∧ Nonempty (_root_.Formalism.L2.Host.Omg H) := by
  intro R H
  refine ⟨⟨⟨fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose,
    fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose_spec⟩⟩, ?_⟩
  have : ∀ k : Fin 2, ∃ f : (ZMod (H.g k))ˣ →* ℂˣ, Function.Injective f := fun k =>
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    exists_injective_units_zmod_hom_units_complex (H.g k)
  exact ⟨⟨fun k => (this k).choose, fun k => (this k).choose_spec⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongrOfAbsNormPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory

theorem localUnit_div_congr_one {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) (y : 𝓞 L)
    (hy : Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y) < 1) :
    y ∉ v.asIdeal ∧ ∃ k : Lˣ, (k : L) = (y : L) ∧
      Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1)
        ≤ WithZero.exp (-1 : ℤ) := by
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
  have hy1 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) = 1 := by
    rw [← hx']
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hx']
    exact hy
  have hy2 : v.valuation L (algebraMap (𝓞 L) L y) = 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap, ← ReciprocityTheory.Aut.adic_algebraMap_R]
    exact hy1
  have hnot : y ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mp hy2
  have hy0 : (y : L) ≠ 0 := by
    intro h
    apply hnot
    have : y = 0 := by exact_mod_cast h
    rw [this]
    exact v.asIdeal.zero_mem
  refine ⟨hnot, Units.mk0 (y : L) hy0, rfl, ?_⟩
  have hk : ((atFin v (Units.mk0 (y : L) hy0) : (v.adicCompletion L)ˣ) : v.adicCompletion L)
      = algebraMap (𝓞 L) (v.adicCompletion L) y := rfl
  have hne : algebraMap (𝓞 L) (v.adicCompletion L) y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  have e : ((x * (atFin v (Units.mk0 (y : L) hy0))⁻¹ : (v.adicCompletion L)ˣ) :
      v.adicCompletion L) - 1 = ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y)
        * (algebraMap (𝓞 L) (v.adicCompletion L) y)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hk, sub_mul, mul_inv_cancel₀ hne]
  rw [e, map_mul, map_inv₀, hy1, inv_one, mul_one]
  generalize Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y) = g at hy
  by_cases hg : g = 0
  · rw [hg]; exact zero_le
  · rw [← WithZero.exp_log hg] at hy ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
    rw [WithZero.exp_le_exp]
    omega

theorem exists_nat_congr_of_absNorm_prime {L : Type} [Field L] [NumberField L]
    (I : Ideal (𝓞 L)) (hI : I ≠ ⊤) {p : ℕ} (hp : p.Prime) (hN : Ideal.absNorm I = p) (y : 𝓞 L) :
    ∃ a : ℕ, y - (a : 𝓞 L) ∈ I := by
  have := Fact.mk hp
  have hcard : Nat.card (𝓞 L ⧸ I) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have : Nontrivial (𝓞 L ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have h := mem_multiples_of_prime_card hcard (g := (1 : 𝓞 L ⧸ I))
    (g' := Ideal.Quotient.mk I y) one_ne_zero
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, map_natCast, ← ha]
  simp


open Classical in
theorem localUnit_congr_global :
    ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ), IsUnitAt v x → (∃ (k : Lˣ) (y : 𝓞 L), (k : L) = (y : L) ∧ y ∉ v.asIdeal ∧ Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ)) ∧ ∀ p : ℕ, p.Prime → Ideal.absNorm v.asIdeal = p → ∃ (a : ℕ) (k : Lˣ), a.Coprime p ∧ (k : L) = (a : L) ∧ Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) := by
  intro L _ _ v x hx
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v (x : v.adicCompletion L) (le_of_eq hx)
  refine ⟨?_, fun p hp hN => ?_⟩
  · obtain ⟨h1, k, hk, h2⟩ := localUnit_div_congr_one v x hx y hy
    exact ⟨k, y, hk, h1, h2⟩
  · obtain ⟨a, ha⟩ := exists_nat_congr_of_absNorm_prime v.asIdeal v.isPrime.ne_top hp hN y
    have hya : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L))) < 1 := by
      have h3 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L)))
          = v.valuation L (algebraMap (𝓞 L) L (y - (a : 𝓞 L))) :=
        ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L (y - (a : 𝓞 L)))
      rw [h3]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr ha
    have hxa : Valued.v ((x : v.adicCompletion L)
        - algebraMap (𝓞 L) (v.adicCompletion L) (a : 𝓞 L)) < 1 := by
      have e : (x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) (a : 𝓞 L)
          = ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y)
            + algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L)) := by
        rw [map_sub]; ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hy hya)
    obtain ⟨h1, k, hk, h2⟩ := localUnit_div_congr_one v x hx (a : 𝓞 L) hxa
    refine ⟨a, k, ?_, by simpa using hk, h2⟩
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    rintro ⟨c, rfl⟩
    apply h1
    have hpm : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := hN ▸ Ideal.absNorm_mem v.asIdeal
    push_cast
    exact v.asIdeal.mul_mem_right _ hpm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleRigidifiedSquareIsoStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_rigidified_square_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L L' : RigLB G)
    (w : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen →
    ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)), w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (jL : L.L.ι) (jL' : L'.L.ι),
      eSec G (r z) ∈ L.L.U jL → eSec G (r z) ∈ L'.L.U jL' →
      gm r z _ (L.rig.s (fun _ => jL)) ^ 2 =
        gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (L'.rig.s (fun _ => jL')) ^ 2 := by
  first | exact @GlobalTheory.RigSq.exists_rescale | exact GlobalTheory.RigSq.exists_rescale | (intros; apply GlobalTheory.RigSq.exists_rescale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_generator_through_squareIso : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by
  first | exact @GlobalTheory.SqLB.exists_sq_gen | exact GlobalTheory.SqLB.exists_sq_gen | (intros; apply GlobalTheory.SqLB.exists_sq_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionFlattenStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linComb_pow_section_flatten : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n))), ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  first | exact @GlobalTheory.linComb_pow_pow_sec | exact GlobalTheory.linComb_pow_pow_sec | (intros; apply GlobalTheory.linComb_pow_pow_sec <;> assumption)
end

