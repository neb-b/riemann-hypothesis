module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsLocPres
section
noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

section Coord

variable {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] (η : G →* ℤˣ) (Ψ : G →* Oˣ)
  (r : G →* GG (m := 3) (R := R)) (W : WPres O ℤ R)

def IsCoord (s : W.σ) : Prop :=
  ∃ g a b, W.wt s = wt6 a - wt6 b ∧ W.z s = emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)

def EntHomog : Prop := ∀ g a b, emb (r g) a b ∈ W.part (wt6 a - wt6 b)

end Coord

def boxDef (j : ℤ) : ℕ := if |j| ≤ 1 then 1 else 0

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ H : Type} [Group Γ] [TopologicalSpace Γ]
  [Group H] [TopologicalSpace H]

def IsLocPres {η : H →* ℤˣ} {Ψ : H →* Oˣ} (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) (WB : WPres O ℤ (U.R ⧸ I)) :
    Prop :=
  (∀ s, IsCoord η Ψ (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB s) ∧ EntHomog (push (Ideal.Quotient.mkₐ O I) U.r.hom) WB

variable {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
  {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R}

def BoxPres (B : Univ (BoxCond N ι hι U I)) (WB : WPres O ℤ (U.R ⧸ I)) : Prop :=
  ∃ (W : WPres O ℤ B.R) (i : (U.R ⧸ I) →ₐ[O] B.R) (τ κ : Type) (_ : Fintype τ) (_ : Fintype κ) (e : WB.σ ⊕ τ ≃ W.σ)
    (f : κ → MvPowerSeries W.σ O) (wf : κ → ℤ),
    IsRelPres WB i W e f wf ∧ push (i.comp (Ideal.Quotient.mkₐ O I)) U.r.hom = B.r.hom.comp ι ∧
    (∀ t, IsCoord η Ψ B.r.hom W (e (.inr t))) ∧ EntHomog B.r.hom W ∧
    ∀ j, Nat.card {u // wf u = j} = Nat.card {t // W.wt (e (.inr t)) = j} + boxDef j

end UpperTheory.V.U3
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelIdealFinitenessOfWeightZeroFinite
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem map_sub_map_mem_pow_of_dist_le_zpow_neg {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (J : Ideal R)
    (hl : (l : R) ∈ J) {k : ℕ} (φ : (Fin k → ℤ_[l]) →+ R) (n : ℕ) (v w : Fin k → ℤ_[l])
    (h : dist v w ≤ (l : ℝ) ^ (-(n : ℤ))) : φ v - φ w ∈ J ^ n := by
  have hdiv : ∀ i, ∃ u : ℤ_[l], v i - w i = (l : ℤ_[l]) ^ n * u := by
    intro i
    have hi : ‖v i - w i‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
      rw [← dist_eq_norm]
      exact (dist_le_pi_dist v w i).trans h
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hi
    obtain ⟨u, hu⟩ := hi
    exact ⟨u, hu⟩
  choose u hu using hdiv
  have hvw : v - w = (l ^ n) • u := by
    ext i
    simp [hu i, nsmul_eq_mul]
  rw [← map_sub, hvw, map_nsmul, nsmul_eq_mul]
  refine Ideal.mul_mem_right _ _ ?_
  rw [Nat.cast_pow]
  exact Ideal.pow_mem_pow hl n

private theorem mem_range_of_approx {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (J : Ideal R)
    [IsHausdorff J R] (hl : (l : R) ∈ J) {k : ℕ} (φ : (Fin k → ℤ_[l]) →+ R) (y : R)
    (h : ∀ n : ℕ, ∃ v, y - φ v ∈ J ^ n) : ∃ v, φ v = y := by
  choose v hv using h
  obtain ⟨a, ψ, hψ, htend⟩ := SeqCompactSpace.tendsto_subseq v
  refine ⟨a, ?_⟩
  have hall : ∀ m : ℕ, y - φ a ∈ J ^ m := by
    intro m
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(m : ℤ)) := by
      have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
      exact zpow_pos hl0 _
    have hev1 : ∀ᶠ j in Filter.atTop, (v ∘ ψ) j ∈ Metric.closedBall a ((l : ℝ) ^ (-(m : ℤ))) :=
      htend.eventually (Metric.closedBall_mem_nhds a hpos)
    have hev2 : ∀ᶠ j in Filter.atTop, m ≤ ψ j := hψ.tendsto_atTop.eventually_ge_atTop m
    obtain ⟨j, hj1, hj2⟩ := (hev1.and hev2).exists
    have e1 : y - φ (v (ψ j)) ∈ J ^ m := Ideal.pow_le_pow_right hj2 (hv (ψ j))
    have e2 : φ (v (ψ j)) - φ a ∈ J ^ m := map_sub_map_mem_pow_of_dist_le_zpow_neg J hl φ m _ _ hj1
    have e3 := add_mem e1 e2
    rwa [sub_add_sub_cancel] at e3
  have h0 : y - φ a = 0 := by
    refine IsHausdorff.haus' (I := J) (y - φ a) (fun n => ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hall n
  exact (sub_eq_zero.mp h0).symm

private theorem norm_coe_coefO_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) :
    ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  have hint : IsIntegral ℤ_[l] (x : PadicAlgCl l) := by
    have hx : IsIntegral ℤ_[l] x := Algebra.IsIntegral.isIntegral x
    exact hx.map c.O.val
  obtain ⟨p, hmon, hp⟩ := hint
  by_contra hgt
  push_neg at hgt
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hp
  have hcoef : ∀ i ∈ Finset.range p.natDegree,
      ‖Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l)
        (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ ≤ ‖(x : PadicAlgCl l)‖ ^ i := by
    intro i _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
      exact PadicInt.norm_le_one _
    calc _ ≤ 1 * ‖(x : PadicAlgCl l)‖ ^ i := by gcongr
      _ = _ := one_mul _
  have hlt : ‖∑ i ∈ Finset.range p.natDegree, Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l))
      (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ <
      ‖(x : PadicAlgCl l)‖ ^ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
    · rw [hn]
      simp
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.mpr hn.ne') (fun i => Polynomial.eval₂
          (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i))
      exact lt_of_le_of_lt (hle.trans (hcoef i hi)) (pow_lt_pow_right₀ hgt (Finset.mem_range.mp hi))
  have heq := eq_neg_of_add_eq_zero_left hp
  have hn := congrArg norm heq
  rw [norm_neg, norm_pow] at hn
  linarith

private theorem natCast_not_isUnit {l : ℕ} [Fact l.Prime] (c : Coef l) : ¬ IsUnit (l : c.O) := by
  rintro ⟨u, hu⟩
  have h1 := norm_coe_coefO_le_one c (↑u⁻¹ : c.O)
  have hprod : (l : PadicAlgCl l) * ((↑u⁻¹ : c.O) : PadicAlgCl l) = 1 := by
    have h := congrArg (fun z : c.O => (z : PadicAlgCl l)) (Units.mul_inv u)
    rw [hu] at h
    simpa using h
  have hl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hn := congrArg norm hprod
  rw [norm_mul, norm_one, hl] at hn
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hle : (l : ℝ)⁻¹ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ ≤ (l : ℝ)⁻¹ * 1 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  linarith

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.U3.modelIdeal_finiteness_of_weightZero_finite :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      Module.Finite c.O (weightZeroSubalgebra c.O S.r.hom) → M2 M.𝒜 M.Q.ideal := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl2 hmk hfin
  haveI := c.dvr
  haveI := c.fin
  haveI hH : IsHausdorff (maximalIdeal S.R) S.R := (IsCO.complete (O := c.O) (R := S.R)).toIsHausdorff
  haveI hloc : IsLocalHom (algebraMap c.O S.R) := IsCO.isLocalHom (O := c.O) (R := S.R)
  have hlm : ((l : ℕ) : S.R) ∈ maximalIdeal S.R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply natCast_not_isUnit c
    rw [← map_natCast (algebraMap c.O S.R)] at hu
    exact isUnit_of_map_unit (algebraMap c.O S.R) _ hu
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := c.O) (M := weightZeroSubalgebra c.O S.r.hom)
  obtain ⟨t, o, ho⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  let F : (Fin n × Fin t → ℤ_[l]) → Fin n × Fin t → S.R := fun z q =>
    algebraMap c.O S.R (algebraMap ℤ_[l] c.O (z q) * o q.2) * ((b q.1 : weightZeroSubalgebra c.O S.r.hom) : S.R)
  let φ : (Fin (n * t) → ℤ_[l]) →+ S.R :=
    { toFun := fun v => ∑ q : Fin n × Fin t, F (v ∘ finProdFinEquiv) q
      map_zero' := by simp [F]
      map_add' := by
        intro v w
        simp only [F, Function.comp_apply, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib] }
  have hφB : ∀ v, φ v ∈ weightZeroSubalgebra c.O S.r.hom := by
    intro v
    show (∑ q : Fin n × Fin t, F (v ∘ finProdFinEquiv) q) ∈ _
    refine Subalgebra.sum_mem _ (fun q _ => ?_)
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (b q.1).2
  have hBφ : ∀ x ∈ weightZeroSubalgebra c.O S.r.hom, ∃ v, φ v = x := by
    intro x hx
    have hx' : (⟨x, hx⟩ : weightZeroSubalgebra c.O S.r.hom) ∈ Submodule.span c.O (Set.range b) := by
      rw [hb]
      trivial
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun c.O).mp hx'
    have hz : ∀ i, ∃ z : Fin t → ℤ_[l], ∑ j, z j • o j = a i := by
      intro i
      have hai : a i ∈ Submodule.span ℤ_[l] (Set.range o) := by
        rw [ho]
        trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).mp hai
    choose z hz using hz
    have hx2 : ∑ i, a i • ((b i : weightZeroSubalgebra c.O S.r.hom) : S.R) = x := by
      have h := congrArg Subtype.val ha
      simpa using h
    refine ⟨(fun q : Fin n × Fin t => z q.1 q.2) ∘ finProdFinEquiv.symm, ?_⟩
    show ∑ q : Fin n × Fin t,
      F (((fun q : Fin n × Fin t => z q.1 q.2) ∘ finProdFinEquiv.symm) ∘ finProdFinEquiv) q = x
    have hcomp : ((fun q : Fin n × Fin t => z q.1 q.2) ∘ finProdFinEquiv.symm) ∘ finProdFinEquiv =
        fun q => z q.1 q.2 := by
      funext q
      simp
    rw [hcomp, Fintype.sum_prod_type, ← hx2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [F]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← map_sum, Algebra.smul_def, ← hz i]
    congr 2
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.smul_def]
  have key : ∀ f ∈ M.𝒜 0, M.q f ∈ weightZeroSubalgebra c.O S.r.hom := by
    intro f hf
    obtain ⟨v, hv⟩ := mem_range_of_approx (maximalIdeal S.R) hlm φ (M.q f) (fun m => by
      obtain ⟨y, hy, hdiff⟩ := M.dense 0 f hf m
      have hle : Submodule.span c.O (entMon S.r.hom 0) ≤ Subalgebra.toSubmodule (weightZeroSubalgebra c.O S.r.hom) :=
        Submodule.span_le.mpr (fun z hz => Algebra.subset_adjoin hz)
      obtain ⟨v, hv⟩ := hBφ y (hle hy)
      exact ⟨v, by rw [hv]; exact hdiff⟩)
    rw [← hv]
    exact hφB v
  have hsub : (M.𝒜 0).map M.q.toLinearMap ≤ Subalgebra.toSubmodule (weightZeroSubalgebra c.O S.r.hom) := by
    rintro _ ⟨f, hf, rfl⟩
    exact key f hf
  haveI : Module.Finite c.O (Subalgebra.toSubmodule (weightZeroSubalgebra c.O S.r.hom)) := hfin
  haveI hpir : IsPrincipalIdealRing c.O := c.dvr.toIsPrincipalIdealRing
  haveI hnr : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing
  haveI : IsNoetherian c.O (Subalgebra.toSubmodule (weightZeroSubalgebra c.O S.r.hom)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  have hfg : ((M.𝒜 0).map M.q.toLinearMap).FG := isNoetherian_submodule.mp inferInstance _ hsub
  show (Submodule.map (Ideal.Quotient.mkₐ c.O M.Q.ideal).toLinearMap (M.𝒜 0)).FG
  rw [← M.ker_q]
  refine Submodule.fg_of_fg_map_injective (Ideal.kerLiftAlg M.q).toLinearMap
    (Ideal.kerLiftAlg_injective M.q) ?_
  rw [← Submodule.map_comp]
  convert hfg using 2
  ext a
  simp [Ideal.kerLiftAlg_mk]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelSigns
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

section SlopeTestRemainingChoices

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [IsNoetherianRing R]
  [NormedField K] [IsUltrametricDist K] [Algebra O K]

omit [IsNoetherianRing R] [IsUltrametricDist K] in
private theorem norm_mul_le_of_loc {f : R →ₐ[O] K} (hf : IsLocPt f) (x : R) {z : R} (hz : z ∈ maximalIdeal R) :
    ‖f (x * z)‖ ≤ ‖f z‖ := by
  rw [map_mul, norm_mul]
  by_cases h0 : f z = 0
  · simp [h0]
  have hp : 0 < ‖f z‖ := norm_pos_iff.2 h0
  have hx : ‖f x‖ ≤ 1 := by
    by_contra hx
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖f z‖⁻¹) (not_le.1 hx)
    have h1 := hf (x ^ n * z) (Ideal.mul_mem_left _ _ hz)
    rw [map_mul, map_pow, norm_mul, norm_pow] at h1
    have h2 := mul_lt_mul_of_pos_right hn hp
    rw [inv_mul_cancel₀ hp.ne'] at h2
    exact lt_asymm h1 h2
  exact mul_le_of_le_one_left hp.le hx

private theorem exists_rho {f : R →ₐ[O] K} (hf : IsLocPt f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ maximalIdeal R, ‖f z‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  have hsm : ∀ z ∈ s, z ∈ maximalIdeal R := fun z hz => hs ▸ Submodule.subset_span hz
  have hlt : (s.sup fun z => ‖f z‖₊) < 1 :=
    (Finset.sup_lt_iff (by norm_num)).2 fun z hz => hf z (hsm z hz)
  refine ⟨(s.sup fun z => ‖f z‖₊ : NNReal), NNReal.coe_nonneg _, hlt, fun z hz => ?_⟩
  have key : ∀ x : R, ‖f (x * z)‖ ≤ (s.sup fun z => ‖f z‖₊ : NNReal) := by
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      intro x
      exact (norm_mul_le_of_loc hf x (hsm z hz)).trans (Finset.le_sup (f := fun z => ‖f z‖₊) hz)
    | zero => intro x; simp
    | add a b _ _ ha hb =>
      intro x
      rw [mul_add, map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha x) (hb x))
    | smul a b _ hb =>
      intro x
      rw [smul_eq_mul, ← mul_assoc]
      exact hb _
  simpa using key 1

private theorem exists_pow {f : R →ₐ[O] K} (hf : IsLocPt f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal R ^ n, ‖f z‖ < ε := by
  obtain ⟨ρ, h0, h1, h⟩ := exists_rho hf
  have key : ∀ n : ℕ, ∀ z ∈ maximalIdeal R ^ (n + 1), ‖f z‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (h b hb) (norm_nonneg _) (pow_nonneg h0 _)
      · rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
  exact ⟨n + 1, fun z hz => (key n z hz).trans_lt
    ((pow_le_pow_of_le_one h0 h1.le (Nat.le_succ n)).trans_lt hn)⟩

private theorem eq_of_dense {f f' : R →ₐ[O] K} (hf : IsLocPt f) (hf' : IsLocPt f') (s : K) (x : R)
    (T : Set R) (hT : ∀ y ∈ T, f' y = s * f y)
    (h : ∀ n : ℕ, ∃ y ∈ Submodule.span O T, x - y ∈ maximalIdeal R ^ n) : f' x = s * f x := by
  have hsp : ∀ y ∈ Submodule.span O T, f' y = s * f y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hT z hz
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, mul_add]
    | smul a b _ hb => rw [map_smul, map_smul, hb, mul_smul_comm]
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hs : 0 < ‖s‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow hf (div_pos hε hs)
  obtain ⟨n', hn'⟩ := exists_pow hf' (div_pos hε hs)
  obtain ⟨y, hy, hxy⟩ := h (max n n')
  have e : f' x - s * f x = f' (x - y) - s * f (x - y) := by
    rw [map_sub, map_sub, hsp y hy]; ring
  have a1 := hn _ (Ideal.pow_le_pow_right (le_max_left _ _) hxy)
  have a2 := hn' _ (Ideal.pow_le_pow_right (le_max_right _ _) hxy)
  rw [e, zero_add]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have a3 := mul_le_mul_of_nonneg_left a1.le (norm_nonneg s)
  have a4 : ε / (‖s‖ + 1) + ‖s‖ * (ε / (‖s‖ + 1)) = ε := by field_simp; ring
  linarith

end SlopeTestRemainingChoices

section Mon

variable {O R K Γ : Type} [CommRing O] [CommRing R] [Algebra O R] [Field K] [Algebra O K] [Group Γ]

private theorem mon_zero (r : Γ →* GG (m := 3) (R := R)) (f : R →ₐ[O] K) (e : ℤ)
    (h : ∀ g a b, e * wt a b < 0 → f ((r g).mat a b) = 0) (j : ℤ) (hj : e * j < 0) :
    ∀ y ∈ entMon r j, f y = 0 := by
  rintro y ⟨L, rfl, rfl⟩
  induction L with
  | nil => simp at hj
  | cons s L ih =>
    rw [List.map_cons, List.sum_cons, mul_add] at hj
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases hs : e * wt s.2.1 s.2.2 < 0
    · rw [h _ _ _ hs, zero_mul]
    · rw [ih (by omega), mul_zero]

private theorem mon_tor (r : Γ →* GG (m := 3) (R := R)) (f f' : R →ₐ[O] K) (t : Kˣ)
    (h : ∀ g a b, f' ((r g).mat a b) = ((t ^ wt a b : Kˣ) : K) * f ((r g).mat a b)) (j : ℤ) :
    ∀ y ∈ entMon r j, f' y = ((t ^ j : Kˣ) : K) * f y := by
  rintro y ⟨L, rfl, rfl⟩
  induction L with
  | nil => simp
  | cons s L ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.prod_cons, map_mul, map_mul, h, ih, _root_.zpow_add,
      Units.val_mul]
    ring

private theorem mat_ker (η : Γ →* ℤˣ) (r : Γ →* GG (m := 3) (R := R)) (c : Γ) (hc : η c = -1) (h1 : (r c).mat = 1) (g : Γ) :
    ∃ g' ∈ η.ker, (r g).mat = (r g').mat := by
  rcases Int.units_eq_one_or (η g) with h | h
  · exact ⟨g, h, rfl⟩
  · refine ⟨g * c⁻¹, by simp [MonoidHom.mem_ker, h, hc], ?_⟩
    have hl : (r c).left = 1 := Units.ext h1
    have e : g = g * c⁻¹ * c := by simp
    conv_lhs => rw [e]
    rw [map_mul r _ c, GG.mat, GG.mat, SemidirectProduct.mul_left, hl, map_one, mul_one]

end Mon

theorem UpperTheory.V.U3.model_signs :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f →
        (NegZero M.𝒜 (f.comp M.q) ↔ Upper η (push f S.r.hom)) ∧ (PosZero M.𝒜 (f.comp M.q) ↔ Lower η (push f S.r.hom)) ∧
        ∀ f' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f' → ∀ t : (PadicAlgCl l)ˣ,
          push f' S.r.hom = conjBy (tor _ t) (push f S.r.hom) → f'.comp M.q = act M.𝒜 (tz t) (f.comp M.q) := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M _ hM f hf
  have h1 : (S.r.hom cc).mat = 1 := ((S.rep S.R).1 (AlgHom.id _ _)).1.atc
  have key : ∀ e : ℤ, (∀ j, e * j < 0 → ∀ x ∈ M.𝒜 j, f (M.q x) = 0) ↔
      ∀ g ∈ η.ker, ∀ a b, e * wt a b < 0 → f ((S.r.hom g).mat a b) = 0 := by
    intro e
    constructor
    · intro h g _ a b hab
      obtain ⟨x, hx, hq⟩ := M.ent g a b
      rw [← hq]
      exact h _ hab x hx
    · intro h j hj x hx
      have h' : ∀ g a b, e * wt a b < 0 → f ((S.r.hom g).mat a b) = 0 := by
        intro g a b hab
        obtain ⟨g', hg', e'⟩ := mat_ker η S.r.hom cc hM.ηc h1 g
        rw [e']
        exact h g' hg' a b hab
      have := eq_of_dense hf hf 0 (M.q x) (entMon S.r.hom j)
        (fun y hy => by rw [mon_zero _ f e h' j hj y hy, zero_mul]) (M.dense j x hx)
      rwa [zero_mul] at this
  refine ⟨?_, ?_, fun f' hf' t ht => ?_⟩
  · have := key 1
    simp only [one_mul] at this
    exact this
  · have := key (-1)
    simp only [neg_mul, one_mul, neg_lt_zero] at this
    exact this
  · have h' : ∀ g a b, f' ((S.r.hom g).mat a b) =
        ((t ^ wt a b : (PadicAlgCl l)ˣ) : PadicAlgCl l) * f ((S.r.hom g).mat a b) := by
      intro g a b
      have := (conjBy_tor (push f S.r.hom) t).1 g a b
      rw [← ht] at this
      exact this
    refine AlgHom.ext fun x => ?_
    induction x using DirectSum.Decomposition.inductionOn M.𝒜 with
    | zero => rw [map_zero, map_zero]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | @homogeneous j x =>
      rw [act_of_mem M.𝒜 _ _ x.2]
      exact eq_of_dense hf hf' _ (M.q x) (entMon S.r.hom j) (mon_tor _ f f' t h' j) (M.dense j x x.2)
end

