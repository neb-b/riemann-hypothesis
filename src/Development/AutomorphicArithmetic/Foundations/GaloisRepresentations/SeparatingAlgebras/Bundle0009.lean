module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBound
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

section CoefLeLemmas

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type}

private lemma coefLe_sum {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ a ∈ s, CoefLe ι R (f a)) : CoefLe ι R (∑ a ∈ s, f a) := by
  intro m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.coeff_sum, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR (fun a ha => h a ha m)

private lemma coefLe_mul {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) {p q : MvPolynomial σ ℂ}
    (hp : CoefLe ι R p) (hq : CoefLe ι S q) : CoefLe ι (R * S) (p * q) := by
  classical
  intro m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.coeff_mul, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hR hS) ?_
  intro x _
  rw [map_mul, norm_mul]
  exact mul_le_mul (hp _) (hq _) (norm_nonneg _) hR

private lemma coefLe_one : CoefLe ι 1 (1 : MvPolynomial σ ℂ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

private lemma coefLe_pow {R : ℝ} (hR : 0 ≤ R) {p : MvPolynomial σ ℂ} (hp : CoefLe ι R p) (k : ℕ) :
    CoefLe ι (R ^ k) (p ^ k) := by
  induction k with
  | zero => simpa using coefLe_one ι
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact coefLe_mul ι (pow_nonneg hR _) hR ih hp

private lemma coefLe_prod {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (h : ∀ a ∈ s, CoefLe ι (r a) (f a)) :
    CoefLe ι (∏ a ∈ s, r a) (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefLe_one ι
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coefLe_mul ι (hr a) (Finset.prod_nonneg fun b _ => hr b) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

private lemma coefLe_C_mul_X {c : ℂ} {R : ℝ} (hR : 1 ≤ R) (hc : ‖ι.symm c‖ ≤ R) (v : σ) :
    CoefLe ι R (MvPolynomial.C c * MvPolynomial.X v) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  split_ifs
  · simpa using hc
  · simpa using zero_le_one.trans hR

private lemma coefLe_monomial_image {τ : Type} {y : σ → MvPolynomial τ ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hy : ∀ v, CoefLe ι R (y v)) (m : σ →₀ ℕ) :
    CoefLe ι (R ^ (m.sum fun _ e => e)) (m.prod fun v e => y v ^ e) := by
  have h := coefLe_prod ι m.support (fun v => y v ^ m v) (fun v => R ^ m v)
    (fun _ => pow_nonneg hR _) (fun v _ => coefLe_pow ι hR (hy v) (m v))
  rwa [Finset.prod_pow_eq_pow_sum] at h

end CoefLeLemmas

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.blockBound_pf :
    UpperTheory.Gal.Gen.BlockBound := by
  intro l _ ι T n A R hR hA D x hx h1
  classical
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  set y : T × Fin n × Fin n → MvPolynomial (T × Fin n × Fin n) ℂ :=
    fun v => ∑ b : Fin n, MvPolynomial.C (A v.1 v.2.1 b) * MvPolynomial.X (v.1, (b, v.2.2)) with hydef
  have hy : ∀ v, CoefLe ι R (y v) := fun v =>
    coefLe_sum ι _ _ hR0 fun b _ => coefLe_C_mul_X ι hR (hA _ _ _) _
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ A x =
      ∑ m ∈ x.support, MvPolynomial.C (AddMonoidAlgebra.coeff x m) * (m.prod fun v e => y v ^ e) := by
    conv_lhs => rw [x.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_monomial]
    rfl
  rw [e]
  refine coefLe_sum ι _ _ (pow_nonneg hR0 _) fun m hm k => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, norm_mul]
  have hdeg : (m.sum fun _ e => e) ≤ D := (MvPolynomial.le_totalDegree hm).trans hx
  calc _ ≤ 1 * R ^ (m.sum fun _ e => e) :=
        mul_le_mul (h1 m) (coefLe_monomial_image ι hR0 hy m k) (norm_nonneg _) zero_le_one
    _ ≤ R ^ D := by
        rw [one_mul]
        exact pow_le_pow_right₀ hR hdeg
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DenomBdd
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound

open GlobalTheory.CongW (IntMat)

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private lemma natCast_int (u : HeightOneSpectrum (𝓞 E)) (l : ℕ) :
    (l : u.adicCompletion E) ∈ u.adicCompletionIntegers E :=
  _root_.natCast_mem (u.adicCompletionIntegers E) l

private lemma v_lt_one (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) :
    Valued.v (l : u.adicCompletion E) < 1 := by
  have h := (u.valuation_lt_one_iff_mem (K := E) ((l : ℕ) : 𝓞 E)).2 hu
  have h2 := u.valuedAdicCompletion_eq_valuation (K := E) ((l : ℕ) : 𝓞 E)
  rw [← h2] at h
  simpa using h

private lemma exists_pow_int (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (y : u.adicCompletion E) : ∃ d : ℕ, (l : u.adicCompletion E) ^ d * y ∈ u.adicCompletionIntegers E := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  obtain ⟨d, hd⟩ := exists_pow_lt₀ (v_lt_one u hu) (Units.mk0 _ (inv_ne_zero hv))
  refine ⟨d, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow]
  have h0 : (0 : _) < Valued.v y := zero_lt_iff.2 hv
  have := mul_le_mul_left (le_of_lt hd) (Valued.v y)
  simpa [hv] using this

private lemma intMat_mono (u : HeightOneSpectrum (𝓞 E)) (l : ℕ) (m : Matrix (Fin a) (Fin a) (u.adicCompletion E))
    {d e : ℕ} (hde : d ≤ e) (h : IntMat u ((l : u.adicCompletion E) ^ d • m)) :
    IntMat u ((l : u.adicCompletion E) ^ e • m) := by
  intro i j
  have h1 := h i j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1 ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  rw [pow_add, mul_comm (_ ^ d), mul_assoc]
  exact mul_mem (pow_mem (natCast_int u l) k) h1

private lemma exists_intMat (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (m : Matrix (Fin a) (Fin a) (u.adicCompletion E)) :
    ∃ d : ℕ, IntMat u ((l : u.adicCompletion E) ^ d • m) := by
  choose D hD using fun p : Fin a × Fin a => exists_pow_int u hu (m p.1 p.2)
  refine ⟨Finset.univ.sup D, fun i j => ?_⟩
  have hle : D (i, j) ≤ Finset.univ.sup D := Finset.le_sup (Finset.mem_univ _)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [hk, pow_add, mul_comm (_ ^ D (i, j)), mul_assoc]
  exact mul_mem (pow_mem (natCast_int u l) k) (hD (i, j))

private lemma isOpen_intMat {X : Type*} [TopologicalSpace X] (u : HeightOneSpectrum (𝓞 E)) (c : u.adicCompletion E)
    (f : X → Matrix (Fin a) (Fin a) (u.adicCompletion E)) (hf : Continuous f) :
    IsOpen {x | IntMat u (c • f x)} := by
  have e : {x | IntMat u (c • f x)} = ⋂ i, ⋂ j, {x | c * f x i j ∈ u.adicCompletionIntegers E} := by
    ext x
    simp [IntMat]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  have hc : Continuous fun x => c * f x i j :=
    continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hf))
  exact (GroundTheory.Global.isOpen_adicCompletionIntegers u).preimage hc

end

end UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound

open GlobalTheory.CongW (IntMat) in
open UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound in
theorem UpperTheory.Gal.Gen.denomBdd_pf :
    UpperTheory.Gal.Gen.DenomBdd := by
  intro E _ _ _ l hl n Z hZ
  have hl0 : ((l : ℕ) : 𝓞 E) ≠ 0 := by
    exact_mod_cast hl.ne_zero
  have hS : {u : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ u.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)}) ?_).subset ?_
    · simpa using hl0
    · intro u hu
      exact Ideal.dvd_span_singleton.2 hu
  have hopen : ∀ d : ℕ, IsOpen {g : UA E n | DenomLe l d g} := by
    intro d
    have e : {g : UA E n | DenomLe l d g} = ⋂ u ∈ {u : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ u.asIdeal},
        ({g : UA E n | IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E)))} ∩
        {g : UA E n | IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E)))}) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, DenomLe]
    rw [e]
    refine hS.isOpen_biInter fun u _ => ?_
    exact (isOpen_intMat u _ _ (Units.continuous_val.comp (GlobalTheory.BCT.GlobLev.continuous_cLoc u))).inter
      (isOpen_intMat u _ _ (Units.continuous_coe_inv.comp (GlobalTheory.BCT.GlobLev.continuous_cLoc u)))
  have hmono : ∀ {d e : ℕ}, d ≤ e → ∀ g : UA E n, DenomLe l d g → DenomLe l e g :=
    fun hde g h u hu => ⟨intMat_mono u l _ hde (h u hu).1, intMat_mono u l _ hde (h u hu).2⟩
  have hcover : ∀ g : UA E n, ∃ d : ℕ, DenomLe l d g := by
    intro g
    have h1 : ∀ u : HeightOneSpectrum (𝓞 E), ∃ d : ℕ, ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
        IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))) ∧
        IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))) := by
      intro u
      by_cases hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal
      · obtain ⟨d₁, h₁⟩ := exists_intMat u hu ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))
        obtain ⟨d₂, h₂⟩ := exists_intMat u hu (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))
        exact ⟨max d₁ d₂, fun _ => ⟨intMat_mono u l _ (le_max_left _ _) h₁, intMat_mono u l _ (le_max_right _ _) h₂⟩⟩
      · exact ⟨0, fun h => absurd h hu⟩
    choose D hD using h1
    refine ⟨hS.toFinset.sup D, fun u hu => ?_⟩
    have hle : D u ≤ hS.toFinset.sup D := Finset.le_sup (hS.mem_toFinset.2 hu)
    exact ⟨intMat_mono u l _ hle (hD u hu).1, intMat_mono u l _ hle (hD u hu).2⟩
  obtain ⟨d, hd⟩ := hZ.elim_directed_cover (fun d : ℕ => {g : UA E n | DenomLe l d g}) hopen
    (fun g _ => Set.mem_iUnion.2 (hcover g))
    (directed_of_isDirected_le fun _ _ hde g hg => hmono hde g hg)
  exact ⟨d, fun g hg => hd hg⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DetBound
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private lemma norm_det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hR : 1 ≤ R) (h : ∀ i j, ‖ι.symm (M i j)‖ ≤ R) : ‖ι.symm M.det‖ ≤ R ^ n :=
  _root_.UpperTheory.Reformulated.B.Qh59.norm_det_le ι M R hR h

theorem UpperTheory.Gal.Gen.detBound_pf :
    UpperTheory.Gal.Gen.DetBound := by
  intro l _ ι T _ n lam A R hR h
  have hR0 : (0 : ℝ) ≤ R := zero_le_one.trans hR
  rw [Formalism.L2.DIV.detTw_eq, map_prod, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have h1 := norm_det_le ι ((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).1
  have h2 := norm_det_le ι (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).2
  have hinv : (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det =
      (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [pow_mul]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (lam τ).detShift
  · rw [hk, zpow_natCast, map_pow, norm_pow, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 k
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow, ← hinv, map_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 k
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EqOneOfFinInf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem eq_one_of_fin_inf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {x : UA E a}
    (hf : x ∈ finU (E := E) (n := a)) (hi : x ∈ infU E a) : x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) x.1 = 1 := hf
  have h2 : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hi
  exact Subtype.ext (ga_ext (by rw [h1]; simp) (by rw [h2]; simp))

private theorem cLoc_of_inf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    (w : HeightOneSpectrum (𝓞 E)) {x : UA E a} (hx : x ∈ infU E a) : cLoc w x = 1 := by
  have h2 : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  have e : cLoc w x = Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by
    ext i j
    rfl
  rw [e, h2, map_one]

private theorem conj_form {G : Type} [Group G] {s j g g' γ x c : G} (hj : j * g' = g' * j) (hj2 : j * g = g * j)
    (hxg : g * x = x * g) (hxj : j * x = x * j) (h : s * j * g' = γ * (s * j * g) * x * c) :
    γ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ := by
  have h0 : γ * (s * j * g) = s * j * g' * c⁻¹ * x⁻¹ := by
    rw [h]; group
  have h1 : γ = s * j * g' * c⁻¹ * x⁻¹ * (s * j * g)⁻¹ := eq_mul_inv_of_mul_eq h0
  have hc : Commute x (g⁻¹ * j⁻¹) :=
    (Commute.inv_right (show Commute x g from hxg.symm)).mul_right (Commute.inv_right (show Commute x j from hxj.symm))
  have hq : x⁻¹ * (g⁻¹ * j⁻¹) = g⁻¹ * j⁻¹ * x⁻¹ := (hc.inv_left).eq
  have hq2 : g⁻¹ * j⁻¹ = j⁻¹ * g⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hj2]
  calc γ = s * (j * g') * c⁻¹ * (x⁻¹ * (g⁻¹ * j⁻¹)) * s⁻¹ := by rw [h1]; group
    _ = s * (g' * j) * c⁻¹ * (j⁻¹ * g⁻¹ * x⁻¹) * s⁻¹ := by rw [hj, hq, hq2]
    _ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ := by group

theorem UpperTheory.Gal.Gen.sep_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.LocComm → UpperTheory.Gal.Gen.RatFin → UpperTheory.Gal.Gen.Sep := by
  intro hLev hComm hRat E _ _ _ a w₀ hs K hK J hJ S T hT hinj
  classical
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E a
  have hI : IsCompact (infU E a : Set (UA E a)) := isCompact_iff_compactSpace.2 inferInstance
  obtain ⟨hL0, hmem0, -, -, -, -⟩ := hLev E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have hC0 : IsCompact (lev K w₀ (J 0) : Set (UA E a)) := hL0.compact

  let P : UA E a × UA E a × UA E a × UA E a × UA E a → UA E a :=
    fun q => q.1 * q.2.2.1 * q.2.2.2.1 * q.2.1⁻¹ * q.2.2.2.2 * q.1⁻¹
  let D : Set (UA E a × UA E a × UA E a × UA E a × UA E a) :=
    (S : Set (UA E a)) ×ˢ (T : Set (UA E a)) ×ˢ (T : Set (UA E a)) ×ˢ
      (lev K w₀ (J 0) : Set (UA E a)) ×ˢ (infU E a : Set (UA E a))
  have hD : IsCompact D :=
    S.finite_toSet.isCompact.prod (T.finite_toSet.isCompact.prod (T.finite_toSet.isCompact.prod (hC0.prod hI)))
  have hP : Continuous P := by
    simp only [P]
    fun_prop
  have hR : (P '' D ∩ (ratU E a : Set (UA E a))).Finite := (hRat E a).1 _ (hD.image hP)

  let Y : UA E a × UA E a → GL (Fin a) (w₀.adicCompletion E) := fun q => cLoc w₀ (q.1⁻¹ * q.2 * q.1)
  let F : Set (GL (Fin a) (w₀.adicCompletion E)) :=
    Y '' ((S : Set (UA E a)) ×ˢ ((P '' D ∩ (ratU E a : Set (UA E a))) \ {1}))
  have hF : F.Finite := (S.finite_toSet.prod (hR.subset Set.diff_subset)).image _
  have hne : ∀ y ∈ F, y ≠ 1 := by
    rintro _ ⟨⟨s, γ⟩, ⟨-, ⟨-, hγ⟩, hγ1⟩, rfl⟩ e
    refine hγ1 ((hRat E a).2 w₀ γ hγ ?_)
    simp only [Y, map_mul, map_inv] at e
    have := congrArg (fun t => cLoc w₀ s * t * (cLoc w₀ s)⁻¹) e
    simpa [mul_assoc] using this
  have ev : ∀ y ∈ F, ∀ᶠ n in Filter.atTop, y ∉ J n := by
    intro y hy
    obtain ⟨n, hn⟩ := hJ.small {y}ᶜ (isOpen_compl_singleton.mem_nhds (by simpa using (hne y hy).symm))
    filter_upwards [Filter.eventually_ge_atTop n] with m hm hym
    exact hn (hJ.anti hm hym) rfl
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 ((Set.Finite.eventually_all hF).2 ev)
  refine ⟨n₀, fun n hn y g hg g' hg' γ hγ x hx c hc h => ?_⟩
  obtain ⟨⟨s, hsS⟩, ⟨j, hjL, hjJ⟩⟩ := y
  simp only at h
  obtain ⟨hLn, -, hcl, hck, -, hmono⟩ := hLev E a w₀ hs K hK (J n) (hJ.isOpen n) (hJ.compact n)
  have hcJ : cLoc w₀ c ∈ J n := hcl c hc
  have hcC0 : c ∈ lev K w₀ (J 0) := hmono (J 0) c hc (hJ.anti (Nat.zero_le n) hcJ)
  have hjC0 : j ∈ lev K w₀ (J 0) := (hmem0 j).2 ⟨1, K.one_mem, j, hjL, hjJ, (one_mul j).symm⟩
  have hgF : g ∈ finU (E := E) (n := a) := (hT g hg).1
  have hgF' : g' ∈ finU (E := E) (n := a) := (hT g' hg').1
  have hcF : c ∈ finU (E := E) (n := a) := hLn.fin hc
  have hjF : j ∈ finU (E := E) (n := a) := (Subgroup.mem_inf.1 hjL).1
  have hg1 : cLoc w₀ g = 1 := (hT g hg).2 w₀ (not_apart_self w₀)
  have hg1' : cLoc w₀ g' = 1 := (hT g' hg').2 w₀ (not_apart_self w₀)
  have hx1 : cLoc w₀ x = 1 := cLoc_of_inf w₀ hx
  have hγeq : γ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ :=
    conj_form (hComm E a w₀ j g' hjL (hT g' hg').2) (hComm E a w₀ j g hjL (hT g hg).2)
      (fin_mul_inf hgF hx) (fin_mul_inf hjF hx) h
  have hcloc : cLoc w₀ (s⁻¹ * γ * s) = cLoc w₀ j * (cLoc w₀ c)⁻¹ * (cLoc w₀ j)⁻¹ := by
    have e : s⁻¹ * γ * s = g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ := by
      rw [hγeq]; group
    rw [e]
    simp only [map_mul, map_inv, hg1, hg1', hx1, inv_one, one_mul, mul_one]
  have hin : cLoc w₀ (s⁻¹ * γ * s) ∈ J n := by
    rw [hcloc]
    exact hJ.normal n _ hjJ _ (inv_mem hcJ)
  have hγ1 : γ = 1 := by
    by_contra hne'
    have hγZ : γ ∈ P '' D :=
      ⟨(s, g, g', j * c⁻¹ * j⁻¹, x⁻¹),
        ⟨hsS, hg, hg', mul_mem (mul_mem hjC0 (inv_mem hcC0)) (inv_mem hjC0), inv_mem hx⟩, hγeq.symm⟩
    exact hn₀ n hn _ ⟨(s, γ), ⟨hsS, ⟨hγZ, hγ⟩, hne'⟩, rfl⟩ hin
  subst hγ1
  have h2 : g' = g * x * c := by
    have : s * j * g' = s * j * (g * x * c) := by
      rw [h]; group
    exact mul_left_cancel this
  have hxF : x ∈ finU (E := E) (n := a) := by
    have e : x = g⁻¹ * g' * c⁻¹ := by
      rw [h2]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hgF) hgF') (inv_mem hcF)
  have hxe : x = 1 := eq_one_of_fin_inf hxF hx
  subst hxe
  have h3 : g⁻¹ * g' = c := by
    rw [h2]; group
  have hcK : c ∈ K := hck c hc (by
    rw [← h3, map_mul, map_inv, hg1, hg1', inv_one, one_mul])
  exact hinj g hg g' hg' (h3 ▸ hcK)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.KerOpen
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.kerOpen_pf :
    UpperTheory.Gal.Gen.PowNhds → UpperTheory.Gal.Gen.KerOpen := by
  intro hP E _ _ w a J hJ A _ _ θ
  have hN : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hV := hP E w a (Nat.card A) hN (J : Set (GL (Fin a) (w.adicCompletion E)))
    (hJ.mem_nhds J.one_mem)
  refine ⟨interior ((fun x => x ^ Nat.card A) '' (J : Set (GL (Fin a) (w.adicCompletion E)))),
    isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := interior_subset hx
  have hx' : x = (⟨y, hy⟩ : J) ^ Nat.card A := Subtype.ext (by simpa using hxy.symm)
  rw [hx', map_pow, pow_card_eq_one']
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.OpOfSmul
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem opOf_smul' (c : ℂ) (f : UA E a →₀ ℂ) (φ : UA E a → ℂ) : opOf (RU E a) (c • f) φ = c • opOf (RU E a) f φ := by
  have e : ∀ f : UA E a →₀ ℂ, opOf (RU E a) f φ = Finsupp.linearCombination ℂ (fun g => RU E a g φ) f := fun f =>
    (Finsupp.linearCombination_apply ℂ f).symm
  rw [e, e, map_smul]

theorem part_mono (W : Wt E a) (C : Subgroup (UA E a)) {P Q : Submodule ℂ (UA E a → ℂ) → Prop} (h : ∀ U, P U → Q U) :
    part W C P ≤ part W C Q :=
  iSup₂_le fun π hπ => le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : Q π.V) => π.finPart W ⊓ fixedBy W C) π (h _ hπ) le_rfl

end UpperTheory.Gal.Gen

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RhoBound
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.rhoBound_pf :
    UpperTheory.Gal.Gen.DegLe → UpperTheory.Gal.Gen.BlockBound → UpperTheory.Gal.Gen.DetBound → UpperTheory.Gal.Gen.SizeLe → UpperTheory.Gal.Gen.RhoBound := by
  intro hdeg hblk hdet hsize E _ _ _ l _ ι a W A R hR hA x hx m
  have hx' : (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ).totalDegree
      ≤ ∑ τ, ∑ i, (W τ).natW i := hdeg (InfinitePlace E) a W x x.2
  have hb := hblk l ι (InfinitePlace E) a (fun τ => ((A τ : Matrix (Fin a) (Fin a) ℂ)).transpose) R hR
    (fun τ i j => (hA τ j i).1) _ x hx' hx m
  have hd := hdet l ι (InfinitePlace E) a W A R hR hA
  have hs := hsize E a W
  have hcoe : (((Formalism.L2.DIV.rhoK W) A) x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ)
      = Formalism.L2.DIV.detTwK W A • Formalism.L2.DIV.trAct A (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ) := rfl
  rw [hcoe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, norm_mul]
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  calc ‖ι.symm (Formalism.L2.DIV.detTwK W A)‖ * ‖ι.symm (AddMonoidAlgebra.coeff (Formalism.L2.DIV.trAct A (x : MvPolynomial _ ℂ)) m)‖
      ≤ R ^ (∑ τ, a * (W τ).detShift.natAbs) * R ^ (∑ τ, ∑ i, (W τ).natW i) :=
        mul_le_mul hd hb (norm_nonneg _) (pow_nonneg hR0 _)
    _ = R ^ (∑ τ, ∑ i, (W τ).natW i + ∑ τ, a * (W τ).detShift.natAbs) := by
        rw [← pow_add, add_comm]
    _ ≤ R ^ (a * GlobalTheory.CongW.wtSize W.at) := pow_le_pow_right₀ hR hs
end

