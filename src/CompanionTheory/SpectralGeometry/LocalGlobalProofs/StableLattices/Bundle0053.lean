module

public import Mathlib
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BicommutantRestrictionPrime
section
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DirectFactor

theorem bicommutant_restriction_prime :
    ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ x y : H →L[ℂ] H,
    (∀ T : H →L[ℂ] H, (∀ g, T * π (j g) = π (j g) * T) → T * y = y * T) → y ≠ 0 →
    (∀ g, x * π (j g) * y = 0) → x = 0 := by
  intro G G₁ H _ _ _ _ π hπ j p hp hc x y hy hy0 hxy
  let W₀ : Submodule ℂ H := Submodule.span ℂ (Set.range fun q : G₁ × H => π (j q.1) (y q.2))
  have hgen : ∀ (g' : G₁) (h : H), π (j g') (y h) ∈ W₀ := fun g' h =>
    Submodule.subset_span ⟨(g', h), rfl⟩
  have hinv : ∀ g, ∀ v ∈ W₀, π g v ∈ W₀ := by
    intro g v hv
    obtain ⟨k, hk, hg⟩ : ∃ k, p k = 1 ∧ g = j (p g) * k :=
      ⟨(j (p g))⁻¹ * g, by simp [hp], by simp⟩
    have hpg : π g = π (j (p g)) * π k := by
      have := congrArg π hg
      rwa [map_mul] at this
    have hKB : ∀ g', π k * π (j g') = π (j g') * π k := fun g' => by
      rw [← map_mul, ← map_mul, (hc g' k hk).eq]
    have hKy : π k * y = y * π k := hy (π k) hKB
    have a1 : ∀ v, π k (y v) = y (π k v) := fun v => DFunLike.congr_fun hKy v
    have a2 : ∀ g' v, π k (π (j g') v) = π (j g') (π k v) := fun g' v =>
      DFunLike.congr_fun (hKB g') v
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨g', h⟩, rfl⟩ := hv
      have e : π g (π (j g') (y h)) = π (j (p g * g')) (y (π k h)) := by
        rw [hpg, map_mul, map_mul]
        simp only [ContinuousLinearMap.mul_apply, a1, a2]
      simpa only [e] using hgen (p g * g') (π k h)
    | zero => simp
    | add u w _ _ hu hw => simpa only [map_add (f := _)] using W₀.add_mem hu hw
    | smul c u _ hu => simpa only [map_smul] using W₀.smul_mem c hu
  have hker : W₀.topologicalClosure ≤ LinearMap.ker (x : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker x)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g', h⟩, rfl⟩
    exact DFunLike.congr_fun (hxy g') h
  rcases hπ.2 _ (isSubrep_topologicalClosure hinv) with hbot | htop
  · exfalso
    apply hy0
    ext h
    have hm : y h ∈ W₀.topologicalClosure := by
      apply Submodule.le_topologicalClosure
      simpa using hgen 1 h
    rw [hbot] at hm
    simpa using hm
  · ext h
    have hm : h ∈ W₀.topologicalClosure := by rw [htop]; trivial
    simpa using hker hm

end GlobalTheory.CompanionTheory.DirectFactor
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DefinitenessStatement
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter Matrix
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DefiniteForm

open CompanionTheory.Rg.Fl

theorem cT_congr {R : Type} [CommRing R] (s : R →+* R) {n : ℕ}
    (Q Qi D J J' Δ : Matrix (Fin n) (Fin n) R) (hQ : Q * Qi = 1)
    (h1 : Formalism.UG.cT s Q * J * Q = Δ) (h2 : Formalism.UG.cT s D * J' * D = Δ) :
    Formalism.UG.cT s (D * Qi) * J' * (D * Qi) = J := by
  calc Formalism.UG.cT s (D * Qi) * J' * (D * Qi)
      = Formalism.UG.cT s Qi * (Formalism.UG.cT s D * J' * D) * Qi := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT s Qi * (Formalism.UG.cT s Q * J * Q) * Qi := by rw [h1, h2]
    _ = Formalism.UG.cT s (Q * Qi) * J * (Q * Qi) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_large_sq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (a : Fin n → F) (ha : ∀ i, a i ≠ 0) (B : ℝ) :
    ∃ N : ℕ, B < N ∧ ∀ i, ∃ c : v.adicCompletion F,
      c * c * algebraMap F (v.adicCompletion F) (a i) = algebraMap F (v.adicCompletion F) (a i + N) := by
  set M : ℕ := Ideal.absNorm v.asIdeal with hM
  have hM0 : M ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hM1 : M ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hM2 : 1 < M := by omega
  have hmem : ((M : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  have hval : Valued.v ((M : ℕ) : v.adicCompletion F) < 1 := by
    have e : ((M : ℕ) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F ((M : ℕ) : 𝓞 F)) := by simp
    have e2 : ∀ y : F, Valued.v (algebraMap F (v.adicCompletion F) y) = v.valuation F y :=
      fun y => v.valuedAdicCompletion_eq_valuation' y
    rw [e, e2]
    exact (v.valuation_lt_one_iff_mem _).2 hmem
  have h4 : Valued.v (4 : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).2 (by
    have h : algebraMap F (v.adicCompletion F) 4 ≠ 0 := (map_ne_zero _).2 (by norm_num)
    rwa [map_ofNat] at h)
  have hA : ∀ i, algebraMap F (v.adicCompletion F) (a i) ≠ 0 := fun i =>
    (map_ne_zero _).2 (ha i)
  have hev : ∀ i, ∀ᶠ k : ℕ in atTop, Valued.v ((M : ℕ) : v.adicCompletion F) ^ k <
      Valued.v (4 : v.adicCompletion F) * Valued.v (algebraMap F (v.adicCompletion F) (a i)) := by
    intro i
    have hne : Valued.v (4 : v.adicCompletion F) * Valued.v (algebraMap F (v.adicCompletion F) (a i)) ≠ 0 :=
      mul_ne_zero h4 ((Valuation.ne_zero_iff _).2 (hA i))
    obtain ⟨K, hK⟩ := exists_pow_lt₀ hval (Units.mk0 _ hne)
    exact eventually_atTop.2 ⟨K, fun k hk => lt_of_le_of_lt (pow_le_pow_right_of_le_one' hval.le hk) hK⟩
  have hbig : ∀ᶠ k : ℕ in atTop, B < ((M ^ k : ℕ) : ℝ) := by
    have : Tendsto (fun k : ℕ => ((M : ℝ)) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hM2)
    filter_upwards [this.eventually_gt_atTop B] with k hk
    push_cast
    exact hk
  obtain ⟨k, hk1, hk2⟩ := (hbig.and (eventually_all.2 hev)).exists
  refine ⟨M ^ k, hk1, fun i => ?_⟩
  obtain ⟨c, hc⟩ := GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v
    (1 + ((M : ℕ) : v.adicCompletion F) ^ k / algebraMap F (v.adicCompletion F) (a i)) (by
      rw [add_sub_cancel_left, map_div₀, map_pow]
      exact (div_lt_iff₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hA i)))).2 (hk2 i))
  refine ⟨c, ?_⟩
  rw [← hc, map_add (f := _), map_natCast]
  have := hA i
  push_cast
  field_simp

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}

theorem isHermND_diagonal (e : Fin n → F) (he : ∀ i, e i ≠ 0) :
    IsHermND σ (diagonal fun i => algebraMap F E (e i)) := by
  refine ⟨fun i j => ?_, ?_⟩
  · by_cases h : i = j
    · subst h
      simp
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h), map_zero]
  · rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero _).2 (he i)

theorem isPosDef_diagonal (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (e : Fin n → F)
    (he : ∀ (τ : E →+* ℂ) i, 0 < (τ (algebraMap F E (e i))).re) :
    IsPosDef σ (diagonal fun i => algebraMap F E (e i)) := by
  intro x hx τ
  have hre : ∀ i, (τ (σ (x i) * (algebraMap F E (e i) * x i))).re =
      Complex.normSq (τ (x i)) * (τ (algebraMap F E (e i))).re := by
    intro i
    rw [map_mul, map_mul, hσ τ]
    have : star (τ (x i)) * (τ (algebraMap F E (e i)) * τ (x i)) =
        ((Complex.normSq (τ (x i)) : ℝ) : ℂ) * τ (algebraMap F E (e i)) := by
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
      ring
    rw [this, Complex.re_ofReal_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec_diagonal, map_sum, Complex.re_sum, hre]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  refine Finset.sum_pos' (fun j _ => mul_nonneg (Complex.normSq_nonneg _) (he τ j).le)
    ⟨i, Finset.mem_univ _, mul_pos (Complex.normSq_pos.2 ?_) (he τ i)⟩
  simpa using hi

end Forms

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]

theorem sigR_includeLeft (x : R) :
    sigR R σ (Algebra.TensorProduct.includeLeft (S := F) (R := F) (A := R) (B := E) x) =
      Algebra.TensorProduct.includeLeft (S := F) (R := F) (A := R) (B := E) x := by
  simp [sigR]

theorem sigR_inclR (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR]

theorem inclR_algebraMap (f : F) :
    inclR R (algebraMap F E f) =
      Algebra.TensorProduct.includeLeft (S := F) (R := F) (A := R) (B := E) (algebraMap F R f) := by
  change Algebra.TensorProduct.includeRight (algebraMap F E f) = _
  rw [AlgHom.commutes, AlgHom.commutes]

end Tensor

theorem locIso {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hinv : ∀ x, σ (σ x) = x) {n : ℕ} (J P : Matrix (Fin n) (Fin n) E) (hP : P.det ≠ 0) (a e : Fin n → F)
    (hPd : Pᵀ * J * P.map σ = diagonal fun i => algebraMap F E (a i)) (v : HeightOneSpectrum (𝓞 F))
    (c : Fin n → Fv F v) (hc0 : ∀ i, c i ≠ 0)
    (hc : ∀ i, c i * c i * algebraMap F (Fv F v) (a i) = algebraMap F (Fv F v) (e i)) :
    Nonempty (GlobalTheory.AdelicU.GLoc σ J v ≃ₜ* GlobalTheory.AdelicU.GLoc σ (diagonal fun i => algebraMap F E (e i)) v) := by
  set φ : E →+* Fv F v ⊗[F] E := inclR (Fv F v) with hφ
  set s : Fv F v ⊗[F] E →+* Fv F v ⊗[F] E := sigR (Fv F v) σ with hs
  let ι : Fv F v →ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.includeLeft
  have hsι : ∀ x, s (ι x) = ι x := sigR_includeLeft σ (Fv F v)
  have hsφ : ∀ x, s (φ x) = φ (σ x) := sigR_inclR σ (Fv F v)
  have hφι : ∀ f : F, φ (algebraMap F E f) = ι (algebraMap F (Fv F v) f) := inclR_algebraMap (Fv F v)
  set Q : Matrix (Fin n) (Fin n) E := P.map σ with hQdef
  have hQdet : Q.det ≠ 0 := by
    have h := RingHom.map_det (σ : E →+* E) P
    rw [RingHom.mapMatrix_apply] at h
    change Q.det ≠ 0 at *
    have h' : Q.det = σ P.det := h.symm
    rw [h']
    exact (map_ne_zero (σ : E →+* E)).2 hP
  have hQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.2 hQdet)
  have hQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.2 hQdet)
  set D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := diagonal fun i => ι (c i)⁻¹ with hD
  set D' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := diagonal fun i => ι (c i) with hD'
  have hDD : D * D' = 1 := by
    rw [hD, hD', diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    rw [← map_mul, inv_mul_cancel₀ (hc0 i), map_one]
  have hDD' : D' * D = 1 := by
    rw [hD, hD', diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    rw [← map_mul, mul_inv_cancel₀ (hc0 i), map_one]
  have hm : ∀ A B : Matrix (Fin n) (Fin n) E, (A * B).map φ = A.map φ * B.map φ := fun A B =>
    Matrix.map_mul
  have hone : (1 : Matrix (Fin n) (Fin n) E).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)
  have hQr : Q.map φ * Q⁻¹.map φ = 1 := by rw [← hm, hQ, hone]
  have hQr' : Q⁻¹.map φ * Q.map φ = 1 := by rw [← hm, hQ', hone]
  have h1 : Formalism.UG.cT s (Q.map φ) * JR (F := F) (Fv F v) J * Q.map φ =
      diagonal fun i => φ (algebraMap F E (a i)) := by
    have e1 : Formalism.UG.cT s (Q.map φ) = Pᵀ.map φ := by
      ext i j
      simp [Formalism.UG.cT, hQdef, hsφ, hinv]
    have e2 : JR (F := F) (Fv F v) J = J.map φ := rfl
    rw [e1, e2, ← hm, ← hm, hPd, Matrix.diagonal_map (map_zero φ)]
  have h2 : Formalism.UG.cT s D * JR (F := F) (Fv F v) (diagonal fun i => algebraMap F E (e i)) * D =
      diagonal fun i => φ (algebraMap F E (a i)) := by
    have e1 : Formalism.UG.cT s D = D := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Formalism.UG.cT, hD, hsι]
      · simp [Formalism.UG.cT, hD, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]
    have e2 : JR (F := F) (Fv F v) (diagonal fun i => algebraMap F E (e i)) =
        diagonal fun i => ι (algebraMap F (Fv F v) (e i)) := by
      change (diagonal fun i => algebraMap F E (e i)).map φ = _
      rw [Matrix.diagonal_map (map_zero φ)]
      congr 1
      ext i
      exact hφι _
    rw [e1, e2, hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    rw [hφι, ← map_mul, ← map_mul, ← hc i]
    congr 1
    field_simp [hc0 i]
  obtain ⟨Φ, -⟩ := GlobalTheory.LocIsoConj.exists_locIso σ J (diagonal fun i => algebraMap F E (e i)) v
    (D * Q⁻¹.map φ) (Q.map φ * D') (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (Q.map φ), hQr', Matrix.one_mul, hDD]) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc D', hDD', Matrix.one_mul, hQr])
    (cT_congr s _ _ _ _ _ _ hQr h1 h2)
  exact ⟨Φ⟩

theorem stDefinite : StDefinite := by
  intro F E _ _ _ _ _ σ hc n J hJ v
  obtain ⟨hinv, hfix⟩ := GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hc
  obtain ⟨P, d, hP, hPd, hdf, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) (G := J) two_ne_zero
    (fun t => hinv t) (fun a b => hJ.1 b a)
  choose a ha using fun i => hfix (d i) (hdf i)
  have had : d = fun i => algebraMap F E (a i) := funext fun i => (ha i).symm
  have ha0 : ∀ i, a i ≠ 0 := fun i h => hd0 hJ.2 i (by rw [← ha i, h, map_zero])
  obtain ⟨N, hN, hsq⟩ := exists_large_sq v a ha0 (∑ i, ∑ τ : E →+* ℂ, |(τ (d i)).re|)
  have hpos : ∀ (τ : E →+* ℂ) i, 0 < (τ (algebraMap F E (a i + N))).re := by
    intro τ i
    have hle : |(τ (d i)).re| ≤ ∑ i, ∑ τ : E →+* ℂ, |(τ (d i)).re| :=
      (Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ (d i)).re|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)).trans
      (Finset.single_le_sum (f := fun i => ∑ τ : E →+* ℂ, |(τ (d i)).re|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    have h3 := neg_abs_le (τ (d i)).re
    rw [map_add (f := _), map_add (f := _), ha i, map_natCast, map_natCast, Complex.add_re, Complex.natCast_re]
    linarith
  have he0 : ∀ i, a i + N ≠ 0 := by
    intro i h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hpos τ i
    rw [h, map_zero, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  choose c hc' using hsq
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h
    have := hc' i
    rw [h, zero_mul, zero_mul] at this
    exact (map_ne_zero _).2 (he0 i) this.symm
  refine ⟨diagonal fun i => algebraMap F E (a i + N), isHermND_diagonal σ _ he0,
    isPosDef_diagonal σ hc.2.2.2 _ hpos, ?_⟩
  rw [had] at hPd
  exact locIso σ hinv J P hP a _ hPd v c hc0 hc'

end GlobalTheory.CompanionTheory.DefiniteForm

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsMinimalOfOrthogonalBound
section
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.OrthoFamily

theorem exists_minimal_of_no_family_below
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Set (Submodule ℂ H))
    (hcl : ∀ S ∈ L, IsClosed (S : Set H))
    (hinf : ∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) (n : ℕ) :
    ∀ S ∈ L, S ≠ ⊥ →
      (∀ f : Fin n → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → (∀ i, f i ≤ S) →
        ¬ Pairwise fun i k => f i ⟂ f k) →
      ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact (hS (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
      (fun i => i.elim0)).elim
  | succ n ih =>
    intro S hSL hS0 hS
    by_cases hmin : ∀ T ∈ L, T ≤ S → T = ⊥ ∨ T = S
    · exact ⟨S, hSL, hS0, hmin⟩
    · push_neg at hmin
      obtain ⟨T, hTL, hTS, hT0, hTne⟩ := hmin
      refine ih T hTL hT0 ?_
      intro f hfL hf0 hfT hpw
      haveI : CompleteSpace T := (hcl T hTL).completeSpace_coe
      have hR0 : S ⊓ Tᗮ ≠ ⊥ := by
        intro h
        apply hTne
        have hsup := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hTS
        rw [inf_comm, h, sup_bot_eq] at hsup
        exact hsup
      have ho : ∀ j, (S ⊓ Tᗮ) ⟂ f j := fun j => inf_le_right.trans (Submodule.orthogonal_le (hfT j))
      apply hS (Fin.cons (S ⊓ Tᗮ) f)
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hinf S hSL T hTL
        | succ j => rw [Fin.cons_succ]; exact hfL j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hR0
        | succ j => rw [Fin.cons_succ]; exact hf0 j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact inf_le_left
        | succ j => rw [Fin.cons_succ]; exact (hfT j).trans hTS
      · intro i k hik
        induction i using Fin.cases with
        | zero =>
          induction k using Fin.cases with
          | zero => exact absurd rfl hik
          | succ j =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact ho j
        | succ j =>
          induction k using Fin.cases with
          | zero =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact (ho j).symm
          | succ j' =>
            rw [Fin.cons_succ, Fin.cons_succ]
            exact hpw (fun h => hik (congrArg Fin.succ h))

theorem exists_minimal_of_orthogonal_bound :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : Set (Submodule ℂ H)) (m : ℕ)
    (S₀ : Submodule ℂ H), (∀ S ∈ L, IsClosed (S : Set H)) → (∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) → S₀ ∈ L → S₀ ≠ ⊥ →
    (∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → ¬ Pairwise fun i k => f i ⟂ f k) →
    ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  intro H _ _ _ L m S₀ hcl hinf hS₀ hS₀0 hfam
  exact exists_minimal_of_no_family_below L hcl hinf (m + 1) S₀ hS₀ hS₀0
    (fun f hfL hf0 _ => hfam f hfL hf0)

end GlobalTheory.CompanionTheory.OrthoFamily
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsomorphismStatement
section
noncomputable section

open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult

namespace GlobalTheory.CompanionTheory.FactorIso

theorem stIso : StIso := by
  intro G G₁ H _ _ _ _ _ _ π hπ j p hj hpj hc W hW
  haveI := hπ.complete
  have hu : IsUnitaryRep (π.comp j) := isUnitaryRep_comp hπ.unitary hj
  refine ⟨⟨W, hW.1.rep, isIrrUnitary_rep hu hW⟩, ?_⟩
  show isoPart hW.1.rep (π.comp j) ⊤ = ⊤
  have hsub : IsSubrep (π.comp j) (isoPart hW.1.rep (π.comp j) ⊤) := isSubrep_isoPart
  have hker : ∀ k, p k = 1 → ∀ v ∈ isoPart hW.1.rep (π.comp j) ⊤,
      π k v ∈ isoPart hW.1.rep (π.comp j) ⊤ := by
    intro k hk v hv
    have hle : isoPart hW.1.rep (π.comp j) ⊤ ≤
        (isoPart hW.1.rep (π.comp j) ⊤).comap (π k : H →ₗ[ℂ] H) :=
      isoPart_le (hsub.1.preimage (π k).continuous) fun T hT x =>
        apply_mem_isoPart (T := (π k).comp T) (mem_homIn_top.2 fun g y => by
          have hcomm : π k * π (j g) = π (j g) * π k := by
            rw [← map_mul, ← map_mul, (hc g k hk).eq]
          have hT' := hT.2 g y
          simp only [ContinuousLinearMap.comp_apply, hT', MonoidHom.comp_apply]
          exact DFunLike.congr_fun hcomm (T y)) x
    exact hle hv
  have hinv : IsSubrep π (isoPart hW.1.rep (π.comp j) ⊤) := by
    refine ⟨hsub.1, fun g v hv => ?_⟩
    have hg : g = j (p g) * ((j (p g))⁻¹ * g) := by group
    have h1 := hsub.2 (p g) _ (hker ((j (p g))⁻¹ * g) (by simp [hpj]) v hv)
    rw [hg, map_mul]
    simpa using h1
  rcases hπ.irred.2 _ hinv with h | h
  · exfalso
    apply hW.2.1
    rw [eq_bot_iff]
    intro w hw
    have hm : W.subtypeL ∈ homIn hW.1.rep (π.comp j) ⊤ := mem_homIn_top.2 fun _ _ => rfl
    have := apply_mem_isoPart hm ⟨w, hw⟩
    rw [h] at this
    simpa using this
  · exact h

end GlobalTheory.CompanionTheory.FactorIso

end
end

