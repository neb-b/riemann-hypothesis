module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDerivationCotangentIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing Matrix

theorem derivation_mem_of_mem_sq {T : Type} [CommRing T] (P : Ideal T) (D : Derivation ℤ T T)
    {x : T} (hx : x ∈ P ^ 2) : D x ∈ P := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact P.add_mem (P.mul_mem_right _ ha) (P.mul_mem_right _ hb)
  · rw [map_add (f := _)]; exact P.add_mem ha hb

theorem mem_of_derivation_det_not_mem {T : Type} [CommRing T] (P : Ideal T) [P.IsPrime] {h : ℕ}
    (D : Fin h → Derivation ℤ T T) (f : Fin h → T) (hf : ∀ i, f i ∈ P)
    (hdet : (Matrix.of fun i j => D j (f i)).det ∉ P) (b : Fin h → T) (t : T) (ht : t ∉ P)
    (hsum : t * ∑ i, b i * f i ∈ P ^ 2) (i : Fin h) : b i ∈ P := by
  set A : Matrix (Fin h) (Fin h) T := Matrix.of fun i j => D j (f i) with hA

  have hv : ∀ j, (b ᵥ* A) j ∈ P := by
    intro j
    have h1 := derivation_mem_of_mem_sq P (D j) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_sum] at h1
    have h2 : (∑ i, b i * f i) * D j t ∈ P :=
      P.mul_mem_right _ (P.sum_mem fun i _ => P.mul_mem_left _ (hf i))
    have h3 : t * ∑ i, D j (b i * f i) ∈ P := by
      have := P.sub_mem h1 h2; simpa using this
    have h4 : ∑ i, D j (b i * f i) ∈ P :=
      ((Ideal.IsPrime.mem_or_mem inferInstance h3).resolve_left ht)
    have h5 : ∑ i, D j (b i * f i) - ∑ i, f i * D j (b i) = (b ᵥ* A) j := by
      rw [← Finset.sum_sub_distrib]
      simp only [Matrix.vecMul, dotProduct, hA, Matrix.of_apply, Derivation.leibniz, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [← h5]
    exact P.sub_mem h4 (P.sum_mem fun i _ => P.mul_mem_right _ (hf i))

  have hw : (b ᵥ* A ᵥ* A.adjugate) i = A.det * b i := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
      Pi.smul_apply, smul_eq_mul]
  have hmem : (b ᵥ* A ᵥ* A.adjugate) i ∈ P := by
    simp only [Matrix.vecMul, dotProduct]
    exact P.sum_mem fun j _ => P.mul_mem_right _ (hv j)
  rw [hw] at hmem
  exact (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_left hdet

theorem DerivationCotangentIndependent.proof : DerivationCotangentIndependent.Statement := by
  intro T _ P _ h D f hf hdet a hsum i

  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl (Finset.univ : Finset (Fin h)) a
  choose b hb using fun k => hs k (Finset.mem_univ k)

  have hmax : maximalIdeal (Localization.AtPrime P) = P.map (algebraMap T (Localization.AtPrime P)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hsq : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) ∈ (P ^ 2).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_pow, ← hmax]
    have : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) =
        algebraMap T (Localization.AtPrime P) (s : T) * ∑ k, a k * algebraMap T (Localization.AtPrime P) (f k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, Finset.mul_sum, hb, Algebra.smul_def]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hsum
  obtain ⟨⟨⟨y, hy⟩, u⟩, hyu⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)).1 hsq
  rw [← map_mul] at hyu
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).1 hyu
  have hbi : b i ∈ P := by
    refine mem_of_derivation_det_not_mem P D f hf hdet b ((c : T) * (u : T)) ?_ ?_ i
    · exact (P.primeCompl.mul_mem c.2 u.2 : _)
    · have : (c : T) * (u : T) * ∑ k, b k * f k = (c : T) * y := by rw [← hc]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hy

  have hsa : algebraMap T (Localization.AtPrime P) (s : T) * a i ∈ maximalIdeal (Localization.AtPrime P) := by
    rw [← Algebra.smul_def, ← hb i]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hbi
  have hs' : algebraMap T (Localization.AtPrime P) (s : T) ∉ maximalIdeal (Localization.AtPrime P) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]; exact s.2
  exact ((maximalIdeal.isMaximal (Localization.AtPrime P)).isPrime.mem_or_mem hsa).resolve_left hs'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteGermProjectionCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteGermProjectionCover.proof (hopen : IrreducibleGermProjectionOpenNear.Statement)
    (hcov : ProperOpenProjectionCover.Statement) : FiniteGermProjectionCover.Statement := by
  intro σ _ X w d A hX hirr hiso hinj
  obtain ⟨N₀, hN₀, hop⟩ := hopen σ X w d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨interior N₀ ∩ N, Filter.inter_mem (interior_mem_nhds.2 hN₀) (hNo.mem_nhds hwN), ?_⟩
  intro B D hBo hBN hwB hDo hDc hmaps hprop hisoB
  have hBN' : B ⊆ N := fun x hx => (hBN hx).2

  have hzero : X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} := by
    ext z
    constructor
    · rintro ⟨hzX, hzB⟩
      have h1 : z ∈ X ∩ N := ⟨hzX, hBN' hzB⟩
      rw [hXN] at h1
      exact ⟨hzB, h1.2⟩
    · rintro ⟨hzB, hz⟩
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hBN' hzB, hz⟩
      rw [← hXN] at h2
      exact ⟨h2.1, hzB⟩

  have hopB : ∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x) := by
    intro x hx V hV
    have h1 := hop x ⟨hx.1, interior_subset (hBN hx.2).1⟩ (V ∩ B)
      (Filter.inter_mem hV (hBo.mem_nhds hx.2))
    have h2 : X ∩ (V ∩ B) = X ∩ B ∩ V := by
      ext z
      simp only [Set.mem_inter_iff]
      tauto
    rwa [h2] at h1
  obtain ⟨δ, M, hδ, hδne, hcount, hgraph, hdense⟩ :=
    hcov σ X B k f d A D hBo (fun i => (hf i).mono hBN') hzero hDo hDc ⟨A w, hmaps hwB⟩ hmaps hprop hopB
  exact ⟨δ, M, hBo, hwB, hDo, hDc, hmaps, hprop, hisoB, hδ, hδne, hcount, hgraph, hdense⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloEliminate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteModuloEliminate.proof (hG : FiniteModuloGeneralEquation.Statement)
    (hW : WeierstrassDivisionAtPoint.Statement) : FiniteModuloEliminate.Statement := by
  intro σ τ _ _ _ x k f L c hf hfin hpow
  obtain ⟨d, F, hF, hFan, hhF, hFev, hord⟩ := hG σ τ x k f L c hf hfin hpow
  obtain ⟨n, e, he, hgen⟩ := hfin

  set t : (σ → ℂ) → ℂ := fun z => L z c - L x c with ht_def
  have ht : AnalyticAt ℂ t x :=
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c).comp L).analyticAt x).sub analyticAt_const
  let ix : Fin (n * d) → Fin n × Fin d := fun p => finProdFinEquiv.symm p
  refine ⟨n * d, fun p z => t z ^ ((ix p).2 : ℕ) * e (ix p).1 z, fun p => (ht.pow _).mul (he _), ?_⟩
  intro g hg
  obtain ⟨b, h, hb, hh, hev⟩ := hgen g hg
  choose q a hq ha hdiv using fun m => hW τ (L x) c d F (b m) hFan (hb m) hord
  have hLt : Tendsto L (𝓝 x) (𝓝 (L x)) := L.continuous.tendsto x
  refine ⟨fun p y => a (ix p).1 (ix p).2 y, fun i z => h i z + ∑ m, q m (L z) * e m z * hF i z,
    fun p => by simpa using ha (ix p).1 (ix p).2, fun i => ?_, ?_⟩
  · refine (hh i).add (Finset.univ.analyticAt_fun_sum fun m _ => ?_)
    have hqL : AnalyticAt ℂ (fun z => q m (L z)) x := (hq m).comp (L.analyticAt x)
    exact (hqL.mul (he m)).mul (hhF i)
  · have hdivL : ∀ᶠ z in 𝓝 x, ∀ m, b m (L z) = q m (L z) * F (L z) +
        ∑ j : Fin d, a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) :=
      eventually_all.2 fun m => hLt.eventually (hdiv m)
    filter_upwards [hev, hdivL, hFev] with z hz hzd hzF
    rw [hz]
    simp only [hzd, hzF, ContinuousLinearMap.comp_apply]
    have hre : ∀ φ : Fin n × Fin d → ℂ, ∑ p : Fin (n * d), φ (ix p) = ∑ m, ∑ j, φ (m, j) := fun φ => by
      rw [← Fintype.sum_prod_type']
      exact finProdFinEquiv.symm.sum_comp φ
    rw [hre (fun mj => a mj.1 mj.2 (zeroCoordinate c (L z)) * (t z ^ (mj.2 : ℕ) * e mj.1 z))]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ht_def]
    have h1 : ∑ m, (q m (L z) * ∑ i, hF i z * f i z) * e m z =
        ∑ i, ∑ m, q m (L z) * e m z * hF i z * f i z := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
    have h2 : ∀ m (j : Fin d), a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) * e m z =
        a m j (zeroCoordinate c (L z)) * ((L z c - L x c) ^ (j : ℕ) * e m z) := fun m j => by ring
    simp only [h2]
    rw [h1]
    ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloGeneralEquation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Matrix

theorem FiniteModuloGeneralEquation.proof : FiniteModuloGeneralEquation.Statement := by
  intro σ τ _ _ _ x k f L c hf ⟨n, e, he, hfin⟩ ⟨r, h, h', hh, hh', hpow⟩
  classical
  have hproj : ∀ c', AnalyticAt ℂ (fun y : τ → ℂ => y c') (L x) := fun c' =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c').analyticAt _

  let fs : Fin k → analyticAtSubring x := fun i => ⟨f i, hf i⟩
  let es : Fin n → analyticAtSubring x := fun m => ⟨e m, he m⟩
  let hs : Fin k → analyticAtSubring x := fun i => ⟨h i, hh i⟩
  let hs' : τ → analyticAtSubring x := fun c' => ⟨h' c', hh' c'⟩
  let T : analyticAtSubring (L x) := ⟨fun y => (y c - L x c) ^ r, mem_analyticAtSubring.2 (((hproj c).sub analyticAt_const).pow r)⟩
  let D : τ → analyticAtSubring (L x) := fun c' =>
    ⟨fun y => zeroCoordinate c y c' - zeroCoordinate c (L x) c', mem_analyticAtSubring.2 (by
      simp only [zeroCoordinate_apply]
      split_ifs
      · exact analyticAt_const
      · exact (hproj c').sub analyticAt_const)⟩

  choose b kk hb hkk hbk using fun (i : Fin n) (c' : τ) => hfin _ ((hh' c').mul (he i))
  obtain ⟨b1, k1, hb1, hk1, h1eq⟩ := hfin (fun _ => 1) analyticAt_const
  let bs : Fin n → τ → Fin n → analyticAtSubring (L x) := fun i c' j => ⟨b i c' j, hb i c' j⟩
  let b1s : Fin n → analyticAtSubring (L x) := fun m => ⟨b1 m, hb1 m⟩
  let M : Matrix (Fin n) (Fin n) (analyticAtSubring (L x)) :=
    Matrix.of fun i j => (if i = j then T else 0) - ∑ c', bs i c' j * D c'
  refine ⟨r * n, ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ), ?_⟩

  let J : Ideal (holGerms x) := Ideal.span (Set.range fun i => analyticAtGerm x (fs i))
  let ψ : analyticAtSubring x →+* holGerms x ⧸ J := (Ideal.Quotient.mk J).comp (analyticAtGerm x)
  let ψ' : analyticAtSubring (L x) →+* holGerms x ⧸ J := ψ.comp (analyticAtComp x L)
  have hψf : ∀ i, ψ (fs i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  have hψeq : ∀ a b : analyticAtSubring x, (a : (σ → ℂ) → ℂ) =ᶠ[𝓝 x] b → ψ a = ψ b := fun a b hab => by
    simp only [ψ, RingHom.comp_apply, (analyticAtGerm_eq_iff a b).2 hab]
  have R1 : ψ' T = ∑ c', ψ (hs' c') * ψ' (D c') := by
    have := hψeq (analyticAtComp x L T) (∑ i, hs i * fs i + ∑ c', hs' c' * analyticAtComp x L (D c')) (by
      filter_upwards [hpow] with z hz
      simpa [analyticAtComp, T, D, hs, hs', fs] using hz)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [ψ', map_add (f := _), map_sum, map_mul, hψf] using this
  have R2 : ∀ i c', ψ (hs' c') * ψ (es i) = ∑ j, ψ' (bs i c' j) * ψ (es j) := fun i c' => by
    have := hψeq (hs' c' * es i) (∑ j, analyticAtComp x L (bs i c' j) * es j +
      ∑ a, (⟨kk i c' a, hkk i c' a⟩ : analyticAtSubring x) * fs a) (by
      filter_upwards [hbk i c'] with z hz
      simpa [analyticAtComp, bs, es, hs', fs] using hz)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [ψ', map_add (f := _), map_sum, map_mul, hψf] using this
  have R3 : ∑ m, ψ' (b1s m) * ψ (es m) = 1 := by
    have := hψeq 1 (∑ m, analyticAtComp x L (b1s m) * es m +
      ∑ a, (⟨k1 a, hk1 a⟩ : analyticAtSubring x) * fs a) (by
      filter_upwards [h1eq] with z hz
      simpa [analyticAtComp, b1s, es, fs] using hz)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [ψ', map_add (f := _), map_sum, map_mul, hψf] using this.symm

  have hMe : (ψ'.mapMatrix M) *ᵥ (fun j => ψ (es j)) = 0 := by
    funext i
    have hdiag : ∑ j, ψ' (if i = j then T else 0) * ψ (es j) = ψ' T * ψ (es i) := by
      simp [apply_ite ψ']
    have key : ∀ c', ψ (hs' c') * ψ' (D c') * ψ (es i) = ∑ j, ψ' (bs i c' j) * ψ' (D c') * ψ (es j) := by
      intro c'
      rw [mul_right_comm, R2, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, map_sub,
      map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Pi.zero_apply, hdiag, R1, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun c' _ => key c', Finset.sum_comm, sub_eq_zero]
  have hdet : ψ' M.det = 0 := by
    rw [RingHom.map_det]
    exact det_eq_zero_of_mulVec_eq_zero _ _ (fun m => ψ' (b1s m)) hMe R3

  have hmem : analyticAtGerm x (analyticAtComp x L M.det) ∈ J := Ideal.Quotient.eq_zero_iff_mem.1 hdet
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  choose q hq using fun i => analyticAtGerm_surjective x (a i)
  refine ⟨fun i => q i, (M.det).2, fun i => (q i).2, ?_, ?_⟩
  · have hgerm : analyticAtGerm x (∑ i, q i * fs i) = analyticAtGerm x (analyticAtComp x L M.det) := by
      rw [← ha]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_mul, hq]
    filter_upwards [(analyticAtGerm_eq_iff _ _).1 hgerm] with z hz
    simpa [analyticAtComp, fs] using hz.symm

  · have hev : ∀ s : ℂ, ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s) = s ^ (r * n) := by
      intro s
      rw [← analyticAtEval_apply, RingHom.map_det]
      have hdg : (analyticAtEval (L x) (L x + Pi.single c s)).mapMatrix M = Matrix.diagonal fun _ => s ^ r := by
        ext i j
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, map_sub, map_sum, map_mul,
          apply_ite (analyticAtEval (L x) (L x + Pi.single c s)), map_zero, analyticAtEval_apply, Matrix.diagonal_apply]
        have hD : ∀ c', ((D c' : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s) = 0 := by
          intro c'
          simp only [D, zeroCoordinate_apply]
          split_ifs with hc
          · simp
          · simp [hc]
        simp [hD, T]
      rw [hdg, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [show (fun s : ℂ => ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s)) =
      fun s : ℂ => s ^ (r * n) from funext hev]
    exact ((analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).pow _).analyticOrderAt_eq_natCast.2
      ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun s => by simp⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

theorem ringKrullDim_mvPolynomial_complex (d : ℕ) :
    ringKrullDim (MvPolynomial (Fin d) ℂ) = d := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem FiniteProjHomInjective.proof : FiniteProjHomInjective.Statement := by
  intro n d J A _ hdim hfin
  set f : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J := (projHom J A).toRingHom with hf
  have hinj : Function.Injective f := by
    by_contra hni
    rw [injective_iff_map_eq_zero] at hni
    push Not at hni
    obtain ⟨p, hp0, hp⟩ := hni
    let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := f.toAlgebra
    have hint : f.IsIntegral := hfin.to_isIntegral

    let g : PrimeSpectrum (MvPolynomial (Fin n) ℂ ⧸ J) →
        PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin d) ℂ) (Ideal.span {p}) := fun q =>
      ⟨PrimeSpectrum.comap f q, by
        rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
          Set.singleton_subset_iff]
        show f p ∈ q.asIdeal
        rw [hp0]; exact q.asIdeal.zero_mem⟩
    have hg : StrictMono g := by
      intro q₁ q₂ hq
      have hlt : q₁.asIdeal < q₂.asIdeal := hq
      obtain ⟨hle, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp hlt
      show q₁.asIdeal.comap (algebraMap _ _) < q₂.asIdeal.comap (algebraMap _ _)
      exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hx2, hx1⟩ (hint x)
    have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤
        ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ Ideal.span {p}) := by
      rw [ringKrullDim_quotient (Ideal.span {p})]
      exact Order.krullDim_le_of_strictMono g hg
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hp)
    rw [ringKrullDim_mvPolynomial_complex] at h2
    rw [hdim] at h1
    have h3 : ((d : ℕ) : WithBot ℕ∞) + 1 ≤ (d : WithBot ℕ∞) := le_trans (by gcongr) h2
    have h4 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h3
    have h5 : d + 1 ≤ d := by exact_mod_cast h4
    omega
  exact fun a b h => hinj h

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionCluster
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Topology

noncomputable section

namespace FiniteProjectionCluster

variable {n d : ℕ}

theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by
    ext x; simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem exists_monic (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (j : Fin n) :
    ∃ P : Polynomial (MvPolynomial (Fin d) ℂ), P.Monic ∧
      ∀ x ∈ zeroSet J, (P.map (eval (A.mulVec x))).IsRoot (x j) := by
  obtain ⟨P, hPm, hP⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J (X j))
  refine ⟨P, hPm, fun x hx => ?_⟩
  have hf : (projHom J A).toRingHom = (Ideal.Quotient.mk J).comp (pullback A).toRingHom := rfl
  rw [hf, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem] at hP
  have h0 := hx _ hP
  rw [Polynomial.hom_eval₂, eval_X] at h0
  have hcomp : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x) :=
    RingHom.ext (FibreBound.eval_pullback A x)
  rw [hcomp, Polynomial.eval₂_eq_eval_map] at h0
  exact h0

theorem exists_bound (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (c : Fin d → ℂ) (R : ℝ) :
    ∃ C : ℝ, ∀ x ∈ zeroSet J, dist (A.mulVec x) c ≤ R → ‖x‖ ≤ C := by
  choose P hPm hP using exists_monic J A hA
  let g : (Fin d → ℂ) → ℝ := fun y =>
    ∑ j, (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval y ((P j).coeff i)‖)
  have hg : Continuous g :=
    continuous_finsetSum _ fun j _ => continuous_const.add
      (continuous_finsetSum _ fun i _ => (MvPolynomial.continuous_eval _).norm)
  obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun x hx hd => ?_⟩
  have hy : A.mulVec x ∈ Metric.closedBall c R := hd
  have hgC : g (A.mulVec x) ≤ C := (Real.le_norm_self _).trans (hC _ hy)
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hC _ hy))).2 fun j => ?_
  have hj := IndefiniteRowSideFullHecke.ComplexSets.norm_lt_of_isRoot_map_eval (hPm j) (A.mulVec x) (hP j x hx)
  have hle : (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval (A.mulVec x) ((P j).coeff i)‖) ≤
      g (A.mulVec x) :=
    Finset.single_le_sum (f := fun j => 1 + ∑ i ∈ Finset.range (P j).natDegree,
      ‖eval (A.mulVec x) ((P j).coeff i)‖)
      (fun k _ => add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      (Finset.mem_univ j)
  linarith

theorem fibre_finite (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (y : Fin d → ℂ) :
    {x | x ∈ zeroSet J ∧ A.mulVec x = y}.Finite := by
  choose P hPm hP using exists_monic J A hA
  refine (Set.Finite.pi (t := fun j => {a | ((P j).map (eval y)).IsRoot a})
    fun j => Polynomial.finite_setOfPred_isRoot ((hPm j).map _).ne_zero).subset ?_
  rintro x ⟨hx, hxA⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  intro j
  rw [← hxA]
  exact hP j x hx

end FiniteProjectionCluster


open FiniteProjectionCluster in
theorem FiniteProjectionCluster.proof : FiniteProjectionCluster.Statement := by
  intro n d J A w U hA hw hU
  have hcont : Continuous fun x : Fin n → ℂ => A.mulVec x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  obtain ⟨C, hC⟩ := exists_bound J A hA (A.mulVec w) 1
  have hF := fibre_finite J A hA (A.mulVec w)
  obtain ⟨ε0, hε0, hballU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε, ⟨hε, hεlt⟩, hεF⟩ :=
    ((Set.Ioo_infinite hε0).sdiff (hF.image fun x => dist x w)).nonempty
  set K := zeroSet J ∩ {x | dist (A.mulVec x) (A.mulVec w) ≤ 1} ∩ Metric.sphere w ε with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact ((isClosed_zeroSet J).inter (isClosed_le (hcont.dist continuous_const)
        continuous_const)).inter Metric.isClosed_sphere
    · exact (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx =>
        mem_closedBall_zero_iff.2 (hC x hx.1.1 hx.1.2)
  have hT : IsCompact (A.mulVec '' K) := hKc.image hcont
  have hnot : A.mulVec w ∉ A.mulVec '' K := by
    rintro ⟨x, ⟨⟨hx, _⟩, hxs⟩, hxA⟩
    exact hεF ⟨x, ⟨hx, hxA⟩, hxs⟩
  obtain ⟨r0, hr0, hr0T⟩ := Metric.isOpen_iff.1 hT.isClosed.isOpen_compl _ hnot
  refine ⟨min r0 1, Metric.ball w ε, (Metric.closedBall w ε)ᶜ, lt_min hr0 one_pos, Metric.isOpen_ball,
    Metric.isClosed_closedBall.isOpen_compl, Metric.mem_ball_self hε,
    (Metric.ball_subset_ball hεlt.le).trans hballU,
    Set.disjoint_left.2 fun x hx hx' => hx' (Metric.ball_subset_closedBall hx), ?_, ?_⟩
  · rintro x ⟨hx, hxr⟩
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hxr
    by_cases h : dist x w < ε
    · exact Or.inl h
    · refine Or.inr fun hcb => ?_
      have heq : dist x w = ε := le_antisymm hcb (not_lt.1 h)
      have hxK : x ∈ K := ⟨⟨hx, hxr'.le.trans (min_le_right _ _)⟩, heq⟩
      exact hr0T (Metric.mem_ball.2 (hxr'.trans_le (min_le_left _ _))) ⟨x, hxK, rfl⟩
  · refine (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx => ?_
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hx.2
    exact mem_closedBall_zero_iff.2 (hC x hx.1 (hxr'.le.trans (min_le_right _ _)))

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

