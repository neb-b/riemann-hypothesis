module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import GroundTheory.AutomorphicForms.Bundle0023
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCyclicVectorOfSeparable
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.CyclicVector

theorem exists_ne_zero_aeval_mulVec_eq_zero {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (p : K[X]) (hp : Irreducible p) (hd : p ∣ γ.charpoly) :
    ∃ w : Fin n → K, w ≠ 0 ∧ aeval γ p *ᵥ w = 0 := by
  classical
  apply Matrix.exists_mulVec_eq_zero_iff.2
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let f := (Algebra.ofId K L).mapMatrix (m := Fin n)
  let M' : Matrix (Fin n) (Fin n) L := γ.map (algebraMap K L)
  have hf : f (aeval γ p) = aeval M' p := (Polynomial.aeval_algHom_apply f γ p).symm
  have hroot : M'.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hd
  have hs : AdjoinRoot.root p ∈ spectrum L M' := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval M' (p.map (algebraMap K L)) ⟨_, hs, rfl⟩
  rw [aeval_map_algebraMap] at h2
  have h0 : eval (AdjoinRoot.root p) (p.map (algebraMap K L)) = 0 := by
    rw [eval_map, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  beta_reduce at h2
  rw [h0, spectrum.zero_mem_iff] at h2
  have h3 : (aeval M' p).det = 0 := by
    by_contra hne
    exact h2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne))
  have h4 : (algebraMap K L) (aeval γ p).det = 0 := by
    rw [RingHom.map_det, ← h3, ← hf]
    rfl
  exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h4

theorem exists_vector_annihilator_dvd {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v : Fin n → K, ∀ h : K[X], aeval γ h *ᵥ v = 0 → γ.charpoly ∣ h := by
  classical
  set χ := γ.charpoly with hχ
  have hχ0 : χ ≠ 0 := (Matrix.charpoly_monic γ).ne_zero
  have hsq : Squarefree χ := hs.squarefree
  let S : Finset K[X] := (UniqueFactorizationMonoid.normalizedFactors χ).toFinset
  have hSirr : ∀ p ∈ S, Irreducible p := fun p hp =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p (Multiset.mem_toFinset.1 hp)
  have hSdvd : ∀ p ∈ S, p ∣ χ := fun p hp =>
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hp)
  have hw : ∀ p : K[X], ∃ w : Fin n → K, p ∈ S → w ≠ 0 ∧ aeval γ p *ᵥ w = 0 := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨w, h1, h2⟩ := exists_ne_zero_aeval_mulVec_eq_zero γ p (hSirr p hp) (hSdvd p hp)
      exact ⟨w, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose w hw using hw
  refine ⟨∑ p ∈ S, w p, fun h hh => ?_⟩

  have key : ∀ p ∈ S, p ∣ h := by
    intro p hp
    obtain ⟨q, hq⟩ := hSdvd p hp
    have hpi := hSirr p hp
    have hpq : ¬ p ∣ q := by
      rintro ⟨r, rfl⟩
      exact hpi.not_isUnit (hsq p ⟨r, by rw [hq]; ring⟩)
    have hother : ∀ p' ∈ S, p' ≠ p → aeval γ q *ᵥ w p' = 0 := by
      intro p' hp' hne
      have hd : p' ∣ q := by
        have h1 : p' ∣ p * q := hq ▸ hSdvd p' hp'
        rcases (hSirr p' hp').prime.dvd_or_dvd h1 with h2 | h2
        · exfalso
          apply hne
          have hass : Associated p' p := (hSirr p' hp').associated_of_dvd hpi h2
          have e1 := UniqueFactorizationMonoid.normalize_normalized_factor p' (Multiset.mem_toFinset.1 hp')
          have e2 := UniqueFactorizationMonoid.normalize_normalized_factor p (Multiset.mem_toFinset.1 hp)
          rw [← e1, ← e2]
          exact normalize_eq_normalize_iff.2 ⟨hass.dvd, hass.symm.dvd⟩
        · exact h2
      obtain ⟨r, rfl⟩ := hd
      rw [mul_comm p' r, map_mul, ← Matrix.mulVec_mulVec, (hw p' hp').2, Matrix.mulVec_zero]
    have hqv : aeval γ q *ᵥ (∑ p' ∈ S, w p') = aeval γ q *ᵥ w p := by
      rw [Matrix.mulVec_sum, Finset.sum_eq_single_of_mem p hp]
      intro p' hp' hne
      exact hother p' hp' hne
    have hker : aeval γ (h * q) *ᵥ w p = 0 := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ← hqv, Matrix.mulVec_mulVec, ← map_mul, mul_comm h q,
        map_mul, ← Matrix.mulVec_mulVec, hh, Matrix.mulVec_zero]
    by_contra hph
    have hcop : IsCoprime p (h * q) :=
      (hpi.coprime_iff_not_dvd.2 hph).mul_right (hpi.coprime_iff_not_dvd.2 hpq)
    obtain ⟨a, b, hab⟩ := hcop
    apply (hw p hp).1
    have hval := congrArg (fun t => aeval γ t *ᵥ w p) hab
    simp only [map_add (f := _), map_mul, map_one, Matrix.one_mulVec, Matrix.add_mulVec] at hval
    rw [← hval, ← Matrix.mulVec_mulVec, (hw p hp).2, ← Matrix.mulVec_mulVec (M := aeval γ b),
      ← map_mul, hker]
    simp
  by_cases hh0 : h = 0
  · simp [hh0]
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hχ0).1 hsq
  refine (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hχ0 hh0).2
    ((Multiset.le_iff_subset hnd).2 fun p hp => ?_)
  have hpS : p ∈ S := Multiset.mem_toFinset.2 hp
  have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor p hp
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hh0).2 ⟨hSirr p hpS, hnorm, key p hpS⟩

theorem exists_cyclic_vector : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K),
    γ.charpoly.Separable → ∃ v : Fin n → K, ∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v := by
  intro K _ n γ hs
  obtain ⟨v, hv⟩ := exists_vector_annihilator_dvd γ hs
  refine ⟨v, ?_⟩
  let T : K[X] →ₗ[K] (Fin n → K) :=
    { toFun := fun h => aeval γ h *ᵥ v
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  let F : (Fin n → K) →ₗ[K] (Fin n → K) :=
    T ∘ₗ (degreeLT K n).subtype ∘ₗ (degreeLTEquiv K n).symm.toLinearMap
  have hinj : Function.Injective F := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have hd : γ.charpoly ∣ (((degreeLTEquiv K n).symm c : degreeLT K n) : K[X]) := hv _ hc
    have hdeg : (((degreeLTEquiv K n).symm c : degreeLT K n) : K[X]).degree < γ.charpoly.degree := by
      rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
      exact Polynomial.mem_degreeLT.1 ((degreeLTEquiv K n).symm c).2
    have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt hd hdeg
    have h1 : (degreeLTEquiv K n).symm c = 0 := Subtype.ext h0
    simpa using h1
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.1 hinj
  intro y
  obtain ⟨c, hc⟩ := hsurj y
  exact ⟨_, hc.symm⟩

end GlobalTheory.CompanionTheory.TorusCh.CyclicVector
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFixedMkEqOfCommute
section
noncomputable section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.JacquetCentral

theorem exists_fixed_mk_eq_of_commute : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsAdmissible π → ∀ (I N : Subgroup G), IsOpen (I : Set G) → IsCompact (I : Set G) →
    ∀ {M : Type} [Group M] (s : M →* G) (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (M₀ : Subgroup M),
    (∀ d ∈ M₀, s d ∈ I) → ∀ (C : Set G), (∀ g ∈ I, ∃ d ∈ M₀, ∃ x ∈ N, ∃ c ∈ C, g = s d * x * c) →
    (∀ U ∈ 𝓝 (1 : G), ∃ t : M, (∀ d ∈ M₀, t * d = d * t) ∧ ∀ c ∈ C, (s t)⁻¹ * c * s t ∈ U) →
    ∀ y : Jacquet π N, y ∈ fixed (jacquet π N s hs) M₀ → ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = y := by
  intro G V _ _ _ _ _ π hπ I N hIo hIc M _ s hs M₀ hsI C hfac hcon y hy
  obtain ⟨hsm, hfd⟩ := hπ
  have hj : ∀ (m : M) (z : V),
      jacquet π N s hs m ((twKer π N 1).mkQ z) = (twKer π N 1).mkQ (π (s m) z) :=
    fun m z => rfl
  have hfixI : ∀ v ∈ fixed π I, ∀ g ∈ I, π g v = v := by
    intro v hv g hg
    have h := hv ⟨g, hg⟩
    simpa using h
  have hy' : ∀ d ∈ M₀, jacquet π N s hs d y = y := by
    intro d hd
    have h := hy ⟨d, hd⟩
    simpa using h
  have hmul : ∀ (a b : G) (z : V), π a (π b z) = π (a * b) z := fun a b z =>
    (LinearMap.congr_fun (map_mul π a b) z).symm
  have hconj : ∀ (g h : G) (z : V), π g (π h z) = π h (π (h⁻¹ * g * h) z) := by
    intro g h z
    rw [hmul, hmul, show h * (h⁻¹ * g * h) = g * h by simp [mul_assoc]]
  have hN : ∀ x ∈ N, ∀ z : V, (twKer π N 1).mkQ (π x z) = (twKer π N 1).mkQ z := by
    intro x hx z
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨⟨x, hx⟩, z, by simp⟩
  have hstep : ∀ u : V, (∀ c ∈ C, π c u = u) →
      (∀ d ∈ M₀, (twKer π N 1).mkQ (π (s d) u) = (twKer π N 1).mkQ u) →
      ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = (twKer π N 1).mkQ u := by
    intro u hu hd
    refine GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq hsm hIc (twKer π N 1).mkQ u ?_
    intro g hg
    obtain ⟨d, hdM, x, hx, c, hc, rfl⟩ := hfac g hg
    rw [← hmul, ← hmul, hu c hc, ← hj, hN x hx u, hj]
    exact hd d hdM
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (twKer π N 1) y
  have hU : {g : G | π g w = w} ∩ (I : Set G) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem ((hsm w).mem_nhds (by simp)) (hIo.mem_nhds I.one_mem)
  obtain ⟨t, htc, htC⟩ := hcon _ hU
  have hcomm : ∀ d ∈ M₀, ∀ z : V, π (s d) (π (s t) z) = π (s t) (π (s d) z) := by
    intro d hd z
    rw [hmul, hmul, ← map_mul, ← map_mul, htc d hd]
  have hC : ∀ z : V, (∀ c ∈ C, π ((s t)⁻¹ * c * s t) z = z) →
      ∀ c ∈ C, π c (π (s t) z) = π (s t) z := by
    intro z hz c hc
    rw [hconj c (s t) z, hz c hc]
  set W : Submodule ℂ (V ⧸ twKer π N 1) := (fixed π I).map (twKer π N 1).mkQ with hW
  haveI : FiniteDimensional ℂ (fixed π I) := hfd I hIo hIc
  have hWfd : FiniteDimensional ℂ W := by
    rw [hW]
    infer_instance
  have hstepW : ∀ u : V, (∀ c ∈ C, π c u = u) →
      (∀ d ∈ M₀, (twKer π N 1).mkQ (π (s d) u) = (twKer π N 1).mkQ u) →
      (twKer π N 1).mkQ u ∈ W := by
    intro u hu hd
    obtain ⟨v, hv, he⟩ := hstep u hu hd
    exact Submodule.mem_map.2 ⟨v, hv, he⟩
  have hAW : ∀ z ∈ W, jacquet π N s hs t z ∈ W := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hz
    rw [hj]
    apply hstepW
    · exact hC v (fun c hc => hfixI v hv _ (htC c hc).2)
    · intro d hd
      rw [hcomm d hd, hfixI v hv (s d) (hsI d hd)]
  have hAy : jacquet π N s hs t ((twKer π N 1).mkQ w) ∈ W := by
    rw [hj]
    apply hstepW
    · exact hC w (fun c hc => (htC c hc).1)
    · intro d hd
      rw [hcomm d hd, ← hj t (π (s d) w), ← hj t w, ← hj d w, hy' d hd]
  have hinv : ∀ z : Jacquet π N, jacquet π N s hs t⁻¹ (jacquet π N s hs t z) = z := by
    intro z
    have h1 := LinearMap.congr_fun (map_mul (jacquet π N s hs) t⁻¹ t) z
    rw [inv_mul_cancel, map_one] at h1
    exact h1.symm
  let A : W →ₗ[ℂ] W := LinearMap.restrict (jacquet π N s hs t) hAW
  have hAinj : Function.Injective A := by
    intro a b hab
    have h : jacquet π N s hs t (a : V ⧸ twKer π N 1) = jacquet π N s hs t (b : V ⧸ twKer π N 1) :=
      congrArg Subtype.val hab
    apply Subtype.ext
    rw [← hinv (a : V ⧸ twKer π N 1), h, hinv]
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hAinj) ⟨_, hAy⟩
  have hz' : jacquet π N s hs t (z : V ⧸ twKer π N 1) = jacquet π N s hs t ((twKer π N 1).mkQ w) :=
    congrArg Subtype.val hz
  have hzw : (z : V ⧸ twKer π N 1) = (twKer π N 1).mkQ w := by
    rw [← hinv (z : V ⧸ twKer π N 1), hz', hinv]
  have hwW : (twKer π N 1).mkQ w ∈ W := by
    rw [← hzw]
    exact z.2
  obtain ⟨v, hv, hvz⟩ := Submodule.mem_map.1 hwW
  exact ⟨v, hv, hvz⟩

end GlobalTheory.CompanionTheory.JacquetCentral
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvolutionAdjoinNorm
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
  GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.SgRing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_conj (x : E) : conjE E (conjE E x) = x :=
  IsCMField.complexConj_apply_apply E x

def bar (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E := (X.map (conjE E))ᵀ

theorem bar_mul (X Y : Matrix (Fin n) (Fin n) E) : bar (X * Y) = bar Y * bar X := by
  rw [bar, bar, bar, Matrix.map_mul, Matrix.transpose_mul]

theorem bar_add (X Y : Matrix (Fin n) (Fin n) E) : bar (X + Y) = bar X + bar Y := by
  ext i j; simp [bar]

theorem bar_bar (X : Matrix (Fin n) (Fin n) E) : bar (bar X) = X := by
  ext i j; simp [bar, conj_conj]

theorem bar_algebraMap (r : E) :
    bar (algebraMap E (Matrix (Fin n) (Fin n) E) r) = algebraMap E (Matrix (Fin n) (Fin n) E) (conjE E r) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [bar, Matrix.algebraMap_matrix_apply]
  · simp [bar, Matrix.algebraMap_matrix_apply, h, Ne.symm h]

theorem sg_eq (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) : sg d X = d.val * bar X * (d⁻¹ : GL (Fin n) E).val := rfl

theorem nrm_val (d : GL (Fin n) E) : (nrm d).val = d.val * bar (d⁻¹ : GL (Fin n) E).val := rfl

theorem nrm_inv_val (d : GL (Fin n) E) :
    ((nrm d)⁻¹ : GL (Fin n) E).val = bar d.val * (d⁻¹ : GL (Fin n) E).val := rfl

theorem sg_add (d : GL (Fin n) E) (X Y : Matrix (Fin n) (Fin n) E) : sg d (X + Y) = sg d X + sg d Y := by
  rw [sg_eq, sg_eq, sg_eq, bar_add, Matrix.mul_add, Matrix.add_mul]

theorem sg_mul (d : GL (Fin n) E) (X Y : Matrix (Fin n) (Fin n) E) : sg d (X * Y) = sg d Y * sg d X := by
  have h : (d⁻¹ : GL (Fin n) E).val * d.val = 1 := Units.inv_mul d
  calc sg d (X * Y) = d.val * bar Y * 1 * bar X * (d⁻¹ : GL (Fin n) E).val := by
        rw [sg_eq, bar_mul]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = sg d Y * sg d X := by
        rw [← h, sg_eq, sg_eq]; simp only [Matrix.mul_assoc]

theorem sg_algebraMap (d : GL (Fin n) E) (r : E) :
    sg d (algebraMap E (Matrix (Fin n) (Fin n) E) r) = algebraMap E (Matrix (Fin n) (Fin n) E) (conjE E r) := by
  have h : d.val * (d⁻¹ : GL (Fin n) E).val = 1 := Units.mul_inv d
  rw [sg_eq, bar_algebraMap, ← Algebra.commutes, Matrix.mul_assoc, h, Matrix.mul_one]

theorem sg_one (d : GL (Fin n) E) : sg d 1 = 1 := by
  have h := sg_algebraMap d 1
  simpa using h

theorem sg_zero (d : GL (Fin n) E) : sg d 0 = 0 := by
  have h := sg_algebraMap d 0
  simpa using h

theorem sg_nrm (d : GL (Fin n) E) : sg d (nrm d).val = ((nrm d)⁻¹ : GL (Fin n) E).val := by
  have h : d.val * (d⁻¹ : GL (Fin n) E).val = 1 := Units.mul_inv d
  rw [nrm_inv_val, sg_eq, nrm_val, bar_mul, bar_bar, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem sg_sg (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) :
    sg d (sg d X) = (nrm d).val * X * ((nrm d)⁻¹ : GL (Fin n) E).val := by
  rw [nrm_inv_val, nrm_val, sg_eq, sg_eq, bar_mul, bar_mul, bar_bar]
  simp only [Matrix.mul_assoc]


omit [NumberField E] [IsCMField E] in
theorem inv_mem (g : GL (Fin n) E) : (g⁻¹ : GL (Fin n) E).val ∈ Algebra.adjoin E {g.val} := by
  have hdet : g.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  have hc : g.val.charpoly.coeff 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  have hp : aeval g.val g.val.charpoly = 0 := Matrix.aeval_self_charpoly _
  set q : Matrix (Fin n) (Fin n) E := aeval g.val (divX g.val.charpoly) with hq
  have hd : q * g.val + algebraMap E _ (g.val.charpoly.coeff 0) = 0 := by
    have h := congrArg (aeval g.val) (divX_mul_X_add g.val.charpoly)
    rwa [hp, map_add, map_mul, aeval_X, aeval_C] at h
  have hmem : q ∈ Algebra.adjoin E {g.val} := aeval_mem_adjoin_singleton E g.val
  have h1 : (-(g.val.charpoly.coeff 0)⁻¹ • q) * g.val = 1 := by
    rw [Matrix.smul_mul, eq_neg_of_add_eq_zero_left hd, Algebra.algebraMap_eq_smul_one, smul_neg, neg_smul, neg_neg,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : (g⁻¹ : GL (Fin n) E).val = -(g.val.charpoly.coeff 0)⁻¹ • q := by
    calc (g⁻¹ : GL (Fin n) E).val = ((-(g.val.charpoly.coeff 0)⁻¹ • q) * g.val) * (g⁻¹ : GL (Fin n) E).val := by
          rw [h1, Matrix.one_mul]
      _ = -(g.val.charpoly.coeff 0)⁻¹ • q := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h2]
  exact Subalgebra.smul_mem _ hmem _

theorem sg_mem (d : GL (Fin n) E) {x : Matrix (Fin n) (Fin n) E} (hx : x ∈ Algebra.adjoin E {(nrm d).val}) :
    sg d x ∈ Algebra.adjoin E {(nrm d).val} := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.1 hx
    rw [sg_nrm]
    exact inv_mem (nrm d)
  | algebraMap r =>
    rw [sg_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [sg_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [sg_mul]
    exact mul_mem hy hx

omit [NumberField E] [IsCMField E] in
theorem adjoin_comm (γ : Matrix (Fin n) (Fin n) E) {x y : Matrix (Fin n) (Fin n) E}
    (hx : x ∈ Algebra.adjoin E {γ}) (hy : y ∈ Algebra.adjoin E {γ}) : x * y = y * x :=
  pol_comm γ x y ((isPol_iff γ x).2 hx) ((isPol_iff γ y).2 hy)

theorem exists_sgRing (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) :
    ∃ σ : Algebra.adjoin E {(nrm d).val} →+* Algebra.adjoin E {(nrm d).val},
      (∀ x, ((σ x : Algebra.adjoin E {(nrm d).val}) : Matrix (Fin n) (Fin n) E) = sg d x) ∧ ∀ x, σ (σ x) = x := by
  refine ⟨{ toFun := fun x => ⟨sg d x, sg_mem d x.2⟩
            map_one' := Subtype.ext (sg_one d)
            map_zero' := Subtype.ext (sg_zero d)
            map_add' := fun x y => Subtype.ext (sg_add d x y)
            map_mul' := fun x y => Subtype.ext ?_ }, fun x => rfl, fun x => Subtype.ext ?_⟩
  · change sg d (x.val * y.val) = sg d x.val * sg d y.val
    rw [sg_mul]
    exact adjoin_comm _ (sg_mem d y.2) (sg_mem d x.2)
  · change sg d (sg d x.val) = x.val
    have hγ : (nrm d).val ∈ Algebra.adjoin E {(nrm d).val} := Algebra.self_mem_adjoin_singleton E _
    rw [sg_sg, adjoin_comm _ hγ x.2, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.CompanionTheory.TorusCh.SgRing

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialProjectionInvariant
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem aeval_mulVec_mem_of_stable {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) ≤ W) (g : K[X]) :
    ∀ y ∈ W, aeval γ g *ᵥ y ∈ W := by
  have hγ : ∀ y ∈ W, γ *ᵥ y ∈ W := fun y hy =>
    hW ⟨y, hy, by rw [Matrix.toLin'_apply]⟩
  induction g using Polynomial.induction_on with
  | C a =>
    intro y hy
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem a hy
  | add p q hp hq =>
    intro y hy
    rw [map_add (f := _), Matrix.add_mulVec]
    exact W.add_mem (hp y hy) (hq y hy)
  | monomial k a ih =>
    intro y hy
    have : aeval γ (C a * X ^ (k + 1)) = aeval γ (C a * X ^ k) * γ := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    rw [this, ← Matrix.mulVec_mulVec]
    exact ih _ (hγ y hy)

def stableIdeal {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) ≤ W) : Ideal K[X] where
  carrier := {h | aeval γ h *ᵥ v ∈ W}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add (f := _), Matrix.add_mulVec]
    exact W.add_mem ha hb
  zero_mem' := by
    simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
    rw [map_mul, ← Matrix.mulVec_mulVec]
    exact aeval_mulVec_mem_of_stable γ W hW c _ hx

theorem exists_idem_pol_range_eq : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K),
    γ.charpoly.Separable → (∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v) →
    ∀ W : Submodule K (Fin n → K), W.map (Matrix.toLin' γ) ≤ W →
    ∃ π, IsPol γ π ∧ π * π = π ∧ LinearMap.range (Matrix.toLin' π) = W := by
  intro K _ n γ v hsep hcyc W hW
  set I := stableIdeal γ v W hW with hI
  have hmemI : ∀ h : K[X], h ∈ I ↔ aeval γ h *ᵥ v ∈ W := fun h => Iff.rfl
  obtain ⟨w, hw⟩ : ∃ w, I = Ideal.span {w} :=
    ⟨Submodule.IsPrincipal.generator I, (Ideal.span_singleton_generator I).symm⟩
  have hdvd : ∀ h : K[X], aeval γ h *ᵥ v ∈ W ↔ w ∣ h := fun h => by
    rw [← hmemI, hw, Ideal.mem_span_singleton]
  have hχ : aeval γ γ.charpoly = 0 := Matrix.aeval_self_charpoly γ
  obtain ⟨c, hc⟩ : w ∣ γ.charpoly := by
    rw [← hdvd, hχ, Matrix.zero_mulVec]
    exact W.zero_mem
  have hco : IsCoprime w c := Polynomial.Separable.isCoprime (hc ▸ hsep)
  obtain ⟨u, b, hub⟩ := hco
  refine ⟨aeval γ (u * w), ⟨u * w, rfl⟩, ?_, ?_⟩
  · have key : u * w * (u * w) = u * w - u * b * γ.charpoly := by
      linear_combination (u * w) * hub + (u * b) * hc
    rw [← map_mul, key, map_sub, map_mul (aeval γ) (u * b), hχ, mul_zero, sub_zero]
  · apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨h, rfl⟩ := hcyc y
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← map_mul, hdvd]
      exact ⟨u * h, by ring⟩
    · intro y hy
      obtain ⟨h, rfl⟩ := hcyc y
      obtain ⟨g, rfl⟩ := (hdvd h).1 hy
      refine ⟨aeval γ (w * g) *ᵥ v, ?_⟩
      have key : u * w * (w * g) = w * g - g * b * γ.charpoly := by
        linear_combination (w * g) * hub + (g * b) * hc
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← map_mul, key, map_sub,
        map_mul (aeval γ) (g * b), hχ, mul_zero, sub_zero]

end GlobalTheory.CompanionTheory.TorusCh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingInductiveSuccessiveApproximationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifting_inductive_successive_approximation : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ) (e : ℕ), Lifts I H hS n (e + 1) → ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.step_of_lifts | exact GlobalTheory.CompanionTheory.GE.Step.step_of_lifts | (intros; apply GlobalTheory.CompanionTheory.GE.Step.step_of_lifts <;> assumption)
end

