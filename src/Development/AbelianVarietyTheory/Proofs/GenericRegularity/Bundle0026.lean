module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralCongrWeakApproximation
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import ReciprocityTheory.SemistableReduction.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralCongrWeakApproximationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_congr_weak_approximation : ∀ (Ω : Type) [Field Ω] (ι : Type) [Finite ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))), (∀ i, ∃ x, v i x = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) → (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) → ∀ (i₀ : ι) (a : Ω), v i₀ a ≤ 1 → ∃ a' : Ω, (∀ i, v i a' ≤ 1) ∧ v i₀ (a - a') < 1 := by
  first | exact @GlobalTheory.WeakApprox.exists_integral_congr | exact GlobalTheory.WeakApprox.exists_integral_congr | (intros; apply GlobalTheory.WeakApprox.exists_integral_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.ConstRatio

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev Deg (wL : WeightFamilies.Wt D j) (m : ℕ) : Submodule B.KO X.Forms :=
  LinearMap.range (X.inc (addL (wt0 D j) wL m))

theorem deg_mul {m n : ℕ} {x y : X.Forms} (hx : x ∈ Deg X wL m) (hy : y ∈ Deg X wL n) :
    x * y ∈ Deg X wL (m + n) := by
  obtain ⟨F, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hy
  have h : X.inc _ F * X.inc _ G ∈
      LinearMap.range (X.inc (wadd (addL (wt0 D j) wL m) (addL (wt0 D j) wL n))) := by
    obtain ⟨H, hH⟩ := X.inc_mul _ _ F G
    exact ⟨H, hH.symm⟩
  rwa [wadd_addL_addL, zero_weight_add] at h

theorem deg_one (F : B.Cusp j wL) : X.inc wL F ∈ Deg X wL 1 := by
  have h : X.inc wL F ∈ LinearMap.range (X.inc wL) := ⟨F, rfl⟩
  unfold Deg
  rwa [add_zero_weight_one_eq]

theorem deg_wsmul (k : ℕ) (g : B.Cusp j (wsmul k wL)) : X.inc (wsmul k wL) g ∈ Deg X wL k := by
  have h : X.inc _ g ∈ LinearMap.range (X.inc (wsmul k wL)) := ⟨g, rfl⟩
  unfold Deg
  rwa [addL, zero_weight_add]

theorem deg_mul_pow {m : ℕ} {y x : X.Forms} (hy : y ∈ Deg X wL m) (hx : x ∈ Deg X wL 1) (e : ℕ) :
    y * x ^ e ∈ Deg X wL (m + e) := by
  induction e with
  | zero => simpa using hy
  | succ e ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact deg_mul X ih hx

theorem deg_mul_prod (d : Fin N →₀ ℕ) {m : ℕ} {y : X.Forms} (hy : y ∈ Deg X wL m) (s : Finset (Fin N)) :
    y * ∏ i ∈ s, X.inc wL (w i) ^ d i ∈ Deg X wL (m + ∑ i ∈ s, d i) := by
  classical
  refine Finset.induction_on s (by simpa using hy) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  have e1 : y * (X.inc wL (w a) ^ d a * ∏ i ∈ s, X.inc wL (w i) ^ d i) =
      (y * ∏ i ∈ s, X.inc wL (w i) ^ d i) * X.inc wL (w a) ^ d a := by ring
  have e2 : m + (d a + ∑ i ∈ s, d i) = m + ∑ i ∈ s, d i + d a := by ring
  rw [e1, e2]
  exact deg_mul_pow X ih (deg_one X (w a)) (d a)

theorem deg_mul_aeval {k : ℕ} (Pw : MvPolynomial (Fin N) B.KO) (hPw : Pw.IsHomogeneous k) {m : ℕ} {y : X.Forms}
    (hy : y ∈ Deg X wL m) :
    y * MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw ∈ Deg X wL (m + k) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Pw.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, mul_left_comm, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = k := by
    have := hPw (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h := deg_mul_prod X w d hy d.support
  rw [hdeg] at h
  exact h

theorem ratio_large {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (hB : CurveLoc.BirAt X N w gF) (k0 : Fin N) (hk0 : gF (X.inc wL (w k0)) ≠ 0) (a : Ω) :
    ∃ k : ℕ, ∀ m, k < m → ∃ n d : B.Cusp j (addL (wt0 D j) wL m),
      gF (X.inc _ d) ≠ 0 ∧ gF (X.inc _ n) = a * gF (X.inc _ d) := by
  obtain ⟨k, g, Pw, hPw, hne, he⟩ := hB a
  refine ⟨k, fun m hm => ?_⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hm
  have h1 : X.inc wL (w k0) * X.inc wL (w k0) ^ e ∈ Deg X wL (1 + e) :=
    deg_mul_pow X (deg_one X (w k0)) (deg_one X (w k0)) e
  have hd := deg_mul_aeval X w Pw hPw h1
  have hn := deg_mul X h1 (deg_wsmul X k g)
  have e1 : 1 + e + k = k + e + 1 := by ring
  rw [e1] at hd hn
  obtain ⟨d, hd⟩ := hd
  obtain ⟨n, hn⟩ := hn
  have hPv : gF (MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw) =
      MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw :=
    MvPolynomial.comp_aeval_apply (fun i => X.inc wL (w i)) gF Pw
  refine ⟨n, d, ?_, ?_⟩
  · rw [hd, map_mul, map_mul, map_pow, hPv]
    exact mul_ne_zero (mul_ne_zero hk0 (pow_ne_zero _ hk0)) hne
  · rw [hd, hn, map_mul, map_mul gF _ (MvPolynomial.aeval _ Pw), hPv, ← he]
    ring

end GlobalTheory.ConstRatio

namespace GlobalTheory


open ConstRatio in
theorem exists_ratio_forms_at_points : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Pt : Type) [Finite Pt] (U : Pt → Type) [∀ ζ, Field (U ζ)] (ev : ∀ ζ, Rp X la N →+* U ζ) (ι : Type) (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) (Zc : Pt → ι) (jz : ∀ ζ, Ω (Zc ζ) →+* U ζ), (∀ ζ, ∃ k, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc wL (w k))) ≠ 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), gF (Zc ζ) (X.inc u F) = 0 → ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F)) = 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u), jz ζ (gF (Zc ζ) (X.inc u F)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F')) = jz ζ (gF (Zc ζ) (X.inc u F')) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F))) → (∀ Z, CurveLoc.BirAt X N w (gF Z)) → (∀ Z (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ F' : B.Cusp j u, gF Z (X.inc u F') = gF Z (X.inc u F) ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc u F') = 0) → ∀ a : ∀ Z, Ω Z, ∃ (k : ℕ) (F F' : B.Cusp j (addL (wt0 D j) wL k)), ∀ ζ, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) ≠ 0 ∧ ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F)) = jz ζ (a (Zc ζ)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) := by
  intro D B P j X la N wL w Pt _ U _ ev ι Ω _ _ gF Zc jz h1 h2 h3 hB hs a
  classical
  haveI := Fintype.ofFinite Pt
  choose k0 hk0 using h1
  have hg0 : ∀ ζ, gF (Zc ζ) (X.inc wL (w (k0 ζ))) ≠ 0 := fun ζ h => hk0 ζ (h2 ζ wL _ h)
  choose K hK using fun ζ => ratio_large X w (gF (Zc ζ)) (hB _) (k0 ζ) (hg0 ζ) (a _)
  set M : ℕ := Finset.univ.sup K with hM
  have hlt : ∀ ζ, K ζ < 1 + M := fun ζ => by
    have : K ζ ≤ M := Finset.le_sup (f := K) (Finset.mem_univ ζ)
    omega
  have key : ∀ Z, ∃ n d : B.Cusp j (addL (wt0 D j) wL (1 + M)),
      (∀ Z', Z' ≠ Z → gF Z' (X.inc _ n) = 0 ∧ gF Z' (X.inc _ d) = 0) ∧
      (Z ∈ Set.range Zc → gF Z (X.inc _ d) ≠ 0 ∧ gF Z (X.inc _ n) = a Z * gF Z (X.inc _ d)) := by
    intro Z
    by_cases hZ : Z ∈ Set.range Zc
    · obtain ⟨ζ, rfl⟩ := hZ
      obtain ⟨n, d, hd, hn⟩ := hK ζ _ (hlt ζ)
      obtain ⟨n', hn1, hn2⟩ := hs (Zc ζ) _ n
      obtain ⟨d', hd1, hd2⟩ := hs (Zc ζ) _ d
      refine ⟨n', d', fun Z' h => ⟨hn2 Z' h, hd2 Z' h⟩, fun _ => ?_⟩
      rw [hn1, hd1]
      exact ⟨hd, hn⟩
    · exact ⟨0, 0, fun Z' _ => by simp, fun h => absurd h hZ⟩
  choose n d hoff hon using key
  have hsum : ∀ (f : ι → B.Cusp j (addL (wt0 D j) wL (1 + M))),
      (∀ Z Z', Z' ≠ Z → gF Z' (X.inc _ (f Z)) = 0) → ∀ ζ,
      gF (Zc ζ) (X.inc _ (∑ Z ∈ Finset.univ.image Zc, f Z)) = gF (Zc ζ) (X.inc _ (f (Zc ζ))) := by
    intro f hf ζ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    exact Finset.sum_eq_single_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ ζ))
      fun Z _ h => hf Z _ h.symm
  refine ⟨1 + M, ∑ Z ∈ Finset.univ.image Zc, n Z, ∑ Z ∈ Finset.univ.image Zc, d Z, fun ζ => ?_⟩
  have hn := hsum n (fun Z Z' h => (hoff Z Z' h).1) ζ
  have hd := hsum d (fun Z Z' h => (hoff Z Z' h).2) ζ
  obtain ⟨o1, o2⟩ := hon (Zc ζ) ⟨ζ, rfl⟩
  rw [← hd] at o1
  rw [← hd, ← hn] at o2
  generalize (∑ Z ∈ Finset.univ.image Zc, n Z) = F at o2 ⊢
  generalize (∑ Z ∈ Finset.univ.image Zc, d Z) = F' at o1 o2 ⊢
  have hj : jz ζ (gF (Zc ζ) (X.inc _ F')) ≠ 0 := (map_ne_zero _).2 o1
  constructor
  · obtain ⟨G, hG⟩ := deg_mul_pow X (deg_one X (w (k0 ζ))) (deg_one X (w (k0 ζ))) M
    have hev : ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ G)) ≠ 0 := by
      rw [hG, map_mul, map_mul, map_pow, map_pow]
      exact mul_ne_zero (hk0 ζ) (pow_ne_zero _ (hk0 ζ))
    intro h0
    have h := h3 ζ _ F' G
    rw [h0, mul_zero] at h
    exact mul_ne_zero hj hev h
  · have h := h3 ζ _ F F'
    rw [o2, map_mul] at h
    apply mul_left_cancel₀ hj
    rw [← h]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FiniteReducedSection
section
noncomputable section

namespace GlobalTheory.CurveRecord

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

theorem finite_reduced_of_eq {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
    [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K'] [CharZero K] {Dd m : ℕ}
    (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = Dd)
    (v : Fin m → Ω) (k₀ : Fin m) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v k₀)) = Dd)
    (t : Fin (Dd + 1) × Fin m → K') (ht : AlgebraicIndependent K t)
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    FiniteDimensional K' (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) ∧
      IsReduced (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) := by
  have e : a = GenSect.tsec K Kl t v := funext fun i => ha i
  subst e
  have := GenSect.s1T (Kl := Kl) hfg htr v k₀ hv₀ hbig t ht
  unfold GenSect.tJ at this
  exact this


set_option maxHeartbeats 1000000 in
theorem tv_indep {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) [Algebra B.KO (Kp X la N)]
    [IsScalarTower B.KO (X.Kl la) (Kp X la N)] :
    AlgebraicIndependent B.KO (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have h0 := (MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)).map' hinj
  have h1 := h0.map' (f := IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N))
    (IsFractionRing.injective (Op X la N) (Kp X la N))
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic _ (nonZeroDivisors (X.Ol la))
  have h2 := (Algebra.IsAlgebraic.algebraicIndependent_iff (X.Ol la) (X.Kl la)).mp h1
  have h3 := h2.restrictScalars (R := B.KO) (algebraMap B.KO (X.Kl la)).injective
  have hfun : (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) =
      ⇑(IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)) ∘
        (⇑(IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) ∘ MvPolynomial.X) := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, Tv]
  rw [hfun]
  exact h3

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem rzMap_sec_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem map_Jid_eq : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

theorem finite_reduced_record
    (hfg : (⊤ : IntermediateField B.KO Ω).FG) (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j)
    (v : Fin N → Ω) (hv : ∀ k, gF (X.inc wL (w k)) = v k) (k₀ : Fin N) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun k => v k / v k₀)) =
      WeightFamilies.dimY D j) :
    FiniteDimensional (Kp X la N) (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) ∧
      IsReduced (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) := by
  let iK : Algebra B.KO (Kp X la N) :=
    ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  have : IsScalarTower B.KO (X.Kl la) (Kp X la N) := IsScalarTower.of_algebraMap_eq' rfl
  rw [map_Jid_eq]
  exact finite_reduced_of_eq hfg htr v k₀ hv₀ hbig _ (tv_indep X la N)
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i)) (fun i => by rw [rzMap_sec_eq]; simp only [hv])

end Rec

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem finite_reduced_section (hfg : FnFG (T.Q.Xo j) T.Q.c) (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) := by
  intro ka wL wF G S g0 la hH Z
  obtain ⟨-, ⟨-, hB2⟩, -, -⟩ := hH
  obtain ⟨k₀, hk₀, htrZ⟩ := hB2 Z
  exact finite_reduced_record (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w (hfg Z) (htr Z)
    (fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun k => formsEvR_single j hG hT Z _ _) k₀ hk₀ htrZ

end GlobalTheory.CurveRecord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.GaussValuationDensityGenerationLocalisation
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.GaussVal

section
variable {O L U Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L]
  [IsFractionRing O L] [Field U] [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ)


omit [Field L] [Algebra O L] [IsFractionRing O L] in
theorem val_lt_one (g : O →+* U) (h1 : ∀ a, v (g a) ≤ 1) {ϖ : O} (hϖ : Irreducible ϖ) (h2 : v (g ϖ) < 1)
    {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) : v (g a) < 1 := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨y, rfl⟩ := ha
  rw [map_mul, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (h1 y)) h2

theorem isInteger_of_val_le (φ : L →+* U) (h1 : ∀ a, v (φ (algebraMap O L a)) ≤ 1) {ϖ : O} (hϖ : Irreducible ϖ)
    (h2 : v (φ (algebraMap O L ϖ)) < 1) {c : L} (hc : v (φ c) ≤ 1) : ∃ a, algebraMap O L a = c := by
  rcases ValuationRing.isInteger_or_isInteger O c with h | ⟨b, hb⟩
  · exact h
  by_cases hc0 : c = 0
  · exact ⟨0, by simp [hc0]⟩
  by_cases hu : IsUnit b
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
    rw [map_units_inv, hb, inv_inv]
  · exfalso
    have := val_lt_one v (φ.comp (algebraMap O L)) h1 hϖ h2 (a := b) hu
    rw [RingHom.comp_apply, hb] at this
    have h3 : v (φ c) * v (φ c⁻¹) = 1 := by rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc0, map_one, map_one]
    exact absurd h3 (lt_of_le_of_lt (mul_le_of_le_one_left' hc) this).ne
end

theorem val_unit {A U Γ : Type} [CommRing A] [Field U] [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ)
    (g : A →+* U) (h1 : ∀ a, v (g a) ≤ 1) {a : A} (ha : IsUnit a) : v (g a) = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  refine le_antisymm (h1 a) ?_
  have h3 : v (g a) * v (g b) = 1 := by rw [← map_mul, ← map_mul, hb, map_one, map_one]
  exact h3.symm.le.trans (mul_le_of_le_one_right' (h1 b))

theorem exists_approx {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    (c t : la.adicCompletion K) (ht : t ≠ 0) :
    ∃ (a : K) (y : la.adicCompletionIntegers K), c - algebraMap K _ a = t * (y : la.adicCompletion K) := by
  have ho : IsOpen {x : la.adicCompletion K | t⁻¹ * (c - x) ∈ la.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (la.adicCompletion K)).preimage (f := fun x => t⁻¹ * (c - x)) (by fun_prop)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap K la).exists_mem_open ho ⟨c, by simp⟩
  exact ⟨a, ⟨_, ha⟩, by rw [mul_inv_cancel_left₀ ht]⟩

noncomputable section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
  (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

local instance : IsDomain (Op X la N) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors

local instance : Field (Kp X la N) :=
  inferInstanceAs (Field (FractionRing (Op X la N)))

local instance : Algebra (Op X la N) (Kp X la N) :=
  (inferInstance : Algebra (Op X la N) (FractionRing (Op X la N)))

local instance : IsFractionRing (Op X la N) (Kp X la N) :=
  (inferInstance : IsFractionRing (Op X la N) (FractionRing (Op X la N)))

local instance : Algebra (X.Ol la) (Kp X la N) :=
  ((algebraMap (Op X la N) (Kp X la N)).comp (algebraMap (X.Ol la) (Op X la N))).toAlgebra

private theorem gaussIntegerMap_injective :
    Function.Injective (algebraMap (X.Ol la) (Kp X la N)) :=
  (IsFractionRing.injective (Op X la N) (Kp X la N)).comp (Op.algebraMap_injective X la N)

local instance : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (K := X.Kl la) (g := algebraMap (X.Ol la) (Kp X la N))
    (by exact gaussIntegerMap_injective X la N)).toAlgebra

local instance : IsScalarTower (X.Ol la) (X.Kl la) (Kp X la N) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    (IsFractionRing.lift_algebraMap (K := X.Kl la) (gaussIntegerMap_injective X la N) c).symm

local instance : IsScalarTower (X.Ol la) (Op X la N) (Kp X la N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem gauss_dense_gen : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (ψ : Kp X la N →+* U), (∀ a : Op X la N, v (ψ (algebraMap (Op X la N) (Kp X la N) a)) ≤ 1) → v (ψ (algebraMap (Op X la N) (Kp X la N) (unifO X la N))) < 1 → (∀ (f : B.KO →+* U), (∀ a, f a = ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) → ∀ p : MvPolynomial (Idx D j N) B.KO, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) → v (MvPolynomial.eval₂ f (fun q => ψ (algebraMap (Op X la N) (Kp X la N) (Tv X la N q))) p) = 1) ∧ (∀ (c : X.Ol la) (γ : WithZero (Multiplicative ℤ)), γ ≠ 0 → ∃ a : B.KO, v (ψ (algebraMap (X.Ol la) (Kp X la N) c) - ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) < γ) ∧ ∀ S : Subfield U, (∀ c : X.Ol la, ψ (algebraMap (X.Ol la) (Kp X la N) c) ∈ S) → (∀ q, ψ (algebraMap (Op X la N) (Kp X la N) (Tv X la N q)) ∈ S) → ∀ c : Kp X la N, ψ c ∈ S := by
  intro D B P j X la N U _ v ψ h1 h2
  have hϖ : Irreducible (unif X la) :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  have e1 : ∀ c : X.Ol la, algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) c) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (X.Ol la) (Op X la N) c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have eC : ∀ c : X.Ol la, algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C c) =
      algebraMap (X.Ol la) (Op X la N) c := fun c => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  set φ : X.Kl la →+* U := ψ.comp (algebraMap (X.Kl la) (Kp X la N)) with hφ
  have g1 : ∀ a, v (φ (algebraMap (X.Ol la) (X.Kl la) a)) ≤ 1 := fun a => by
    rw [hφ, RingHom.comp_apply, e1]; exact h1 _
  have g2 : v (φ (algebraMap (X.Ol la) (X.Kl la) (unif X la))) < 1 := by
    rw [hφ, RingHom.comp_apply, e1]; exact h2
  refine ⟨?_, ?_, ?_⟩
  · intro f hf p hp ⟨α₀, hα₀⟩
    have hf' : ∀ a, f a = φ (algebraMap B.KO (X.Kl la) a) := hf
    have hex : ∀ α, ∃ a : X.Ol la, algebraMap (X.Ol la) (X.Kl la) a = algebraMap B.KO (X.Kl la) (p.coeff α) :=
      fun α => isInteger_of_val_le v φ g1 hϖ g2 (by rw [← hf']; exact hp α)
    choose b hb using hex
    set p₀ : Pol X la N := ∑ α ∈ p.support, MvPolynomial.monomial α (b α) with hp₀
    have hs : α₀ ∈ p.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h
      rw [h, map_zero, map_zero] at hα₀
      exact zero_ne_one hα₀
    have hc : p₀.coeff α₀ = b α₀ := by
      classical
      rw [hp₀, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_ite_eq', ite_eq_left hs]
    have hn : p₀ ∉ gI X la N := by
      unfold gI Formalism.DV.gaussIdeal
      rw [MvPolynomial.mem_map_C_iff]
      intro h
      have := val_lt_one v (φ.comp (algebraMap (X.Ol la) (X.Kl la))) g1 hϖ g2 (h α₀)
      rw [hc, RingHom.comp_apply, hb, ← hf', hα₀] at this
      exact lt_irrefl _ this
    have hu : IsUnit (algebraMap (Pol X la N) (Op X la N) p₀) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Op X la N) (gI X la N) p₀).2 hn
    have := val_unit v (ψ.comp (algebraMap (Op X la N) (Kp X la N))) h1 hu
    rw [← this]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.eval₂_eq, hp₀, map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.monomial_eq, map_mul, map_mul, eC, hf', ← hb, hφ, RingHom.comp_apply, e1, Finsupp.prod,
      map_prod, map_prod]
    simp only [map_pow]
    rfl
  · intro c γ hγ
    obtain ⟨n, hn⟩ := exists_pow_lt₀ g2 (Units.mk0 γ hγ)
    have ht : algebraMap (X.Ol la) (X.Kl la) (unif X la) ^ n ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact hϖ.ne_zero
    obtain ⟨a, y, hy⟩ := exists_approx la (algebraMap (X.Ol la) (X.Kl la) c) _ ht
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N)]
    change v (φ _ - φ _) < γ
    rw [← map_sub, hy, map_mul, map_mul, map_pow, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (g1 y)) hn
  · intro S hO hT
    have hP : ∀ q : Pol X la N,
        ψ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) q)) ∈ S := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => rw [eC]; exact hO a
      | add p q hp hq => simp only [map_add (f := _)]; exact S.add_mem hp hq
      | mul_X p i hp => simp only [map_mul]; exact S.mul_mem hp (hT i)
    have hA : ∀ x : Op X la N, ψ (algebraMap (Op X la N) (Kp X la N) x) ∈ S := by
      intro x
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (gI X la N).primeCompl x
      have hs : ψ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) s)) ≠ 0 :=
        (((IsLocalization.map_units (Op X la N) s).map _).map _).ne_zero
      have h' := congrArg (fun z => ψ (algebraMap (Op X la N) (Kp X la N) z)) h
      simp only [map_mul] at h'
      rw [eq_div_of_mul_eq hs h']
      exact S.div_mem (hP _) (hP _)
    intro c
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Op X la N) c
    rw [map_div₀]
    exact S.div_mem (hA _) (hA _)

end

end GlobalTheory.GaussVal
end

