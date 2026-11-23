module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalTransitionDetMulConjEqOne
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

noncomputable def hYYLeft (D : D7) {N N' : ℕ} (y : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] D.host.K where
  toFun x := hYY D x y
  map_add' x x' := by
    simp only [hYY, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' c x := by
    simp only [hYY, Matrix.smul_apply, smul_mul_assoc, RingHom.id_apply]
    rw [← map_smul, Finset.smul_sum]
    simp only [Finset.smul_sum]

theorem hYY_herm (D : D7) (h : TraceMapNormalisation D) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D y x : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E)) := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  unfold hYY
  rw [← h, ← h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc, Complex.conj_conj]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem onB_expand (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b)
    (x : Matrix (Fin N') (Fin N) D.host.E) : x = ∑ i, hYY D x (b i) • b i := by
  have hx : x ∈ Submodule.span D.host.K (Set.range b) := by rw [hb.2]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.K).1 hx
  have h1 : ∀ k, hYY D x (b k) = c k := by
    intro k
    change hYYLeft D (b k) x = c k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum]
    have h2 : ∀ i, hYYLeft D (b k) (c i • b i) = if i = k then c i else 0 := by
      intro i
      rw [map_smul]
      change c i • hYY D (b i) (b k) = _
      rw [hb.1 i k]
      split_ifs <;> simp
    simp only [h2]
    simp
  simp only [h1]
  exact hc.symm

theorem onB_parseval (D : D7) (h : TraceMapNormalisation D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : OnB D b) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) =
      ∑ i, D.host.φ₀ ((hYY D x (b i) : D.host.K) : D.host.E) *
        starRingEnd ℂ (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)) := by
  have h1 : hYY D x y = ∑ i, hYY D x (b i) * hYY D (b i) y := by
    change hYYLeft D y x = _
    conv_lhs => rw [onB_expand D b hb x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have h2 := congrArg (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h2
  refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, ← hYY_herm D h y (b i)]
  rfl

theorem det_onB_mul_conj : ∀ (D : D7), admG1 D → ∀ (N N' r : ℕ) (b₀ b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b₀ → OnB D b → (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) * D.host.conj (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) = 1 := by
  intro D hD N N' r b₀ b hb₀ hb
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  set M : Matrix (Fin r) (Fin r) D.host.K := Matrix.of fun i j => hYY D (b j) (b₀ i) with hM
  let ψ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have hA : (ψ.mapMatrix M).transpose * (starRingEnd ℂ).mapMatrix (ψ.mapMatrix M) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    have h1 := onB_parseval D hD.2 b₀ hb₀ (b j) (b k)
    rw [hb.1 j k] at h1
    refine Eq.trans h1.symm ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact map_one ψ
    · exact map_zero ψ
  have hdet := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det (starRingEnd ℂ), ← RingHom.map_det ψ, Matrix.det_one] at hdet
  apply D.host.φ₀.injective
  rw [map_mul, hc, map_one]
  exact hdet

end GlobalTheory.NormSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.PtsMem

theorem inc_injective (D : D7) : Function.Injective (inc D) := by
  haveI : Nontrivial (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 ℚ)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField ℚ)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion ℚ) = 1 := congrArg (fun x : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ => x v) h
    exact zero_ne_one h2
  haveI : Nontrivial (AE D) := by
    have hinj : Function.Injective (Algebra.TensorProduct.includeRight :
        IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AE D) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap ℚ D.host.E).injective
    exact hinj.nontrivial
  exact (inc D).injective

theorem sgA_inc (D : D7) (x : D.host.E) : sgA D (inc D x) = inc D (D.host.conj x) := by
  simp [sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]

theorem mem_GA (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) :
    g ∈ GA D N ↔ ((g : Matrix (Fin N) (Fin N) (AE D)).map (sgA D)).transpose *
      (g : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
  have h1 : (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  change ((g : Matrix (Fin N) (Fin N) (AE D)).map (sgA D)).transpose *
    (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : Matrix (Fin N) (Fin N) (AE D)) =
    (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) ↔ _
  rw [h1, Matrix.mul_one]

theorem map_ct (D : D7) {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) :
    ((γ.map D.host.conj).transpose).map (inc D) = ((γ.map (inc D)).map (sgA D)).transpose := by
  ext i j
  simp [sgA_inc]

theorem unitary_of_isRat (D : D7) {N : ℕ} (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (h : IsRat D (g : GL (Fin N) (AE D)) γ) : γ * (γ.map D.host.conj).transpose = 1 := by
  have hg := (mem_GA D _).1 g.2
  unfold IsRat at h
  rw [h, ← map_ct, ← Matrix.map_mul] at hg
  rw [mul_eq_one_comm]
  apply Matrix.map_injective (inc_injective D)
  simp only
  rw [hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_isRat (D : D7) {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (h : γ * (γ.map D.host.conj).transpose = 1) :
    ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ := by
  have h' : (γ.map D.host.conj).transpose * γ = 1 := mul_eq_one_comm.1 h
  have a : γ.map (inc D) * ((γ.map D.host.conj).transpose).map (inc D) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have b : ((γ.map D.host.conj).transpose).map (inc D) * γ.map (inc D) = 1 := by
    rw [← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨⟨_, _, a, b⟩, (mem_GA D _).2 ?_⟩, rfl⟩
  change ((γ.map (inc D)).map (sgA D)).transpose * γ.map (inc D) = 1
  rw [← map_ct, b]

def ratSub (D : D7) (N : ℕ) : Subgroup (GA D N) where
  carrier := {g | ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ}
  one_mem' := ⟨1, by
    unfold IsRat
    rw [Matrix.map_one _ (map_zero _) (map_one _)]; rfl⟩
  mul_mem' := by
    rintro a b ⟨γ, ha⟩ ⟨γ', hb⟩
    refine ⟨γ * γ', ?_⟩
    unfold IsRat at *
    rw [Matrix.map_mul, ← ha, ← hb]; rfl
  inv_mem' := by
    rintro a ⟨γ, ha⟩
    refine ⟨(γ.map D.host.conj).transpose, ?_⟩
    have hg := (mem_GA D _).1 a.2
    unfold IsRat at *
    rw [map_ct, ← ha]
    exact Units.inv_eq_of_mul_eq_one_left hg

def intSub (D : D7) (N : ℕ) : Subgroup (GA D N) where
  carrier := {k | IntG D (k : GL (Fin N) (AE D))}
  one_mem' := by
    intro i j
    have : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    exact ⟨this, by simpa using this⟩
  mul_mem' := by
    intro a b ha hb i j
    constructor
    · rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (ha i l).1 (hb l j).1
    · rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hb i l).2 (ha l j).2
  inv_mem' := by
    intro a ha i j
    refine ⟨(ha i j).2, ?_⟩
    rw [Subgroup.coe_inv, inv_inv]
    exact (ha i j).1

end GlobalTheory.NormSum.PtsMem


open GlobalTheory.NormSum.PtsMem in
theorem GlobalTheory.NormSum.mem_ratG_intG : ∀ (D : D7) (N : ℕ), (∀ g : GA D N, g ∈ ratG D N ↔ ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ k : GA D N, k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D))) ∧ (∀ γ : Matrix (Fin N) (Fin N) D.host.E, γ * (γ.map D.host.conj).transpose = 1 → ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ (g : GA D N) γ, IsRat D (g : GL (Fin N) (AE D)) γ → γ * (γ.map D.host.conj).transpose = 1) ∧ Function.Injective (inc D) := by
  intro D N
  refine ⟨fun g => ?_, fun k => ?_, exists_isRat D, unitary_of_isRat D, inc_injective D⟩
  · have : ratG D N = ratSub D N := Subgroup.closure_eq (ratSub D N)
    rw [this]; rfl
  · have : intG D N = intSub D N := Subgroup.closure_eq (intSub D N)
    rw [this]; rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SameCharacterCommonExtension
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.Proof.dvr_of_reflects_facts

theorem dvr_of_reflects {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (g : O →+* A) (hg : Function.Injective g)
    (hd : ∀ x y, g x ∣ g y → x ∣ y) (t : O) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    IsDiscreteValuationRing O := by
  haveI : ValuationRing O := ValuationRing.iff_dvd_total.2
    ⟨fun x y => (ValuationRing.dvd_total (g x) (g y)).imp (hd x y) (hd y x)⟩
  haveI : WfDvdMonoid O := by
    refine Subrelation.wf (r := InvImage DvdNotUnit g) ?_ (InvImage.wf g wellFounded_dvdNotUnit)
    rintro x y ⟨hx, c, hc, rfl⟩
    refine ⟨fun h => hx (hg (by simpa using h)), g c, fun h => hc ?_, by simp⟩
    exact isUnit_of_dvd_one (hd c 1 (by simpa using h.dvd))
  haveI : IsPrincipalIdealRing O := ((IsBezout.tfae (R := O)).out 4 2).1 ‹WfDvdMonoid O›
  refine { not_a_field' := fun h => ht0 ?_ }
  have : t ∈ IsLocalRing.maximalIdeal O := ht
  rw [h] at this
  simpa using this

theorem common_of_field {O₀ A B K : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K]
    (fA : O₀ →+* A) (fB : O₀ →+* B) (hAi : fA.IsIntegral) (hB : Function.Injective fB)
    (hBl : IsLocalHom fB) (f₀ : O₀ →+* K) (jA : K →+* FractionRing A) (jB : K →+* FractionRing B)
    (hjA : ∀ c, jA (f₀ c) = algebraMap A _ (fA c)) (hjB : ∀ c, jB (f₀ c) = algebraMap B _ (fB c)) :
    ∃ (O₁ : Subring K) (_ : IsDiscreteValuationRing O₁) (f : O₀ →+* O₁) (gA : O₁ →+* A) (gB : O₁ →+* B),
      (∀ x, x ∈ O₁ ↔ ∃ a, algebraMap A _ a = jA x) ∧
      (∀ x, algebraMap A _ (gA x) = jA x) ∧ (∀ x, algebraMap B _ (gB x) = jB x) ∧
      Function.Injective gA ∧ Function.Injective gB ∧ IsLocalHom gA ∧ IsLocalHom gB ∧
      gA.comp f = fA ∧ gB.comp f = fB := by
  have iA := IsFractionRing.injective A (FractionRing A)
  have iB := IsFractionRing.injective B (FractionRing B)
  let O₁ : Subring K := (algebraMap A (FractionRing A)).range.comap jA
  have hmem : ∀ x, x ∈ O₁ ↔ ∃ a, algebraMap A _ a = jA x := fun x => Iff.rfl
  let f : O₀ →+* O₁ := f₀.codRestrict O₁ (fun c => (hmem _).2 ⟨fA c, (hjA c).symm⟩)
  have hf : ∀ c, (f c : K) = f₀ c := fun c => rfl
  have lift : ∀ {C : Type} [CommRing C] [IsDomain C] (j : K →+* FractionRing C),
      (∀ x : O₁, ∃ a, algebraMap C _ a = j x) → ∃ g : O₁ →+* C, ∀ x, algebraMap C _ (g x) = j x := by
    intro C _ _ j h
    have iC := IsFractionRing.injective C (FractionRing C)
    choose g hg using h
    exact ⟨{ toFun := g
             map_one' := iC (by simp [hg])
             map_mul' := fun x y => iC (by simp [hg])
             map_zero' := iC (by simp [hg])
             map_add' := fun x y => iC (by simp [hg]) }, hg⟩
  obtain ⟨gA, hgA⟩ := lift jA (fun x => (hmem x).1 x.2)
  have gAi : Function.Injective gA := fun x y h =>
    Subtype.ext (jA.injective (by rw [← hgA, ← hgA, h]))
  have cA : gA.comp f = fA := RingHom.ext fun c => iA (by rw [RingHom.comp_apply, hgA, hf, hjA])
  have hint : ∀ x : O₁, ∃ a, algebraMap B _ a = jB x := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hAi (gA x)
    have h1 : p.eval₂ f x = 0 := gAi (by rw [Polynomial.hom_eval₂, cA, hpx, map_zero])
    have h2 := congrArg (jB.comp O₁.subtype) h1
    rw [Polynomial.hom_eval₂, map_zero] at h2
    refine IsIntegrallyClosed.algebraMap_eq_of_integral ⟨p.map fB, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap B (FractionRing B)).comp fB = (jB.comp O₁.subtype).comp f :=
      RingHom.ext fun c => (hjB c).symm
    rw [e]
    exact h2
  obtain ⟨gB, hgB⟩ := lift jB hint
  have gBi : Function.Injective gB := fun x y h =>
    Subtype.ext (jB.injective (by rw [← hgB, ← hgB, h]))
  have cB : gB.comp f = fB := RingHom.ext fun c => iB (by rw [RingHom.comp_apply, hgB, hf, hjB])
  have hd : ∀ x y, gA x ∣ gA y → x ∣ y := by
    rintro x y ⟨c, hc⟩
    by_cases hx : x = 0
    · have : y = 0 := gAi (by rw [hc, hx]; simp)
      simp [this]
    have hx' : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
    have hx'' : jA x ≠ 0 := by simpa using hx'
    refine ⟨⟨y / x, (hmem _).2 ⟨c, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [map_div₀, eq_div_iff hx'', ← hgA, ← hgA, hc, map_mul, mul_comm]
    · simp [mul_div_cancel₀ _ hx']
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
  have hcB : ∀ c, gB (f c) = fB c := fun c => by rw [← cB]; rfl
  have hnu : ¬ IsUnit (gB (f ϖ)) := fun h => hϖ.not_isUnit (hBl.map_nonunit _ (hcB ϖ ▸ h))
  have ht0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hB (by rw [← hcB, h, map_zero, map_zero]))
  haveI hD : IsDiscreteValuationRing O₁ :=
    dvr_of_reflects gA gAi hd (f ϖ) ht0 (fun h => hnu (h.map gB))
  refine ⟨O₁, hD, f, gA, gB, hmem, hgA, hgB, gAi, gBi,
    ⟨fun x h => isUnit_of_dvd_one (hd x 1 (by simpa using h.dvd))⟩, ⟨fun x h => ?_⟩, cA, cB⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O₁
  by_contra hx
  have hπx : π ∣ x := by
    have : x ∈ IsLocalRing.maximalIdeal O₁ := hx
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  have hu : IsUnit (gB π) := isUnit_of_dvd_unit (map_dvd gB hπx) h
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hπ
  apply hnu
  rw [hn, map_mul, map_pow]
  exact (u.isUnit.map gB).mul (hu.pow n)

theorem common : ∀ (Γ O₀ A B : Type) [Group Γ] [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (fA : O₀ →+* A) (fB : O₀ →+* B), Function.Injective fA → fA.IsIntegral → Function.Injective fB → IsLocalHom fB → ∀ (ψA : Γ →* Aˣ) (ψB : Γ →* Bˣ), SameChar fA fB ψA ψB → ∃ (O₁ : Type) (_ : CommRing O₁) (_ : IsDomain O₁) (_ : IsDiscreteValuationRing O₁) (f : O₀ →+* O₁) (gA : O₁ →+* A) (gB : O₁ →+* B) (ψ : Γ →* O₁ˣ), Function.Injective gA ∧ Function.Injective gB ∧ IsLocalHom gA ∧ IsLocalHom gB ∧ gA.comp f = fA ∧ gB.comp f = fB ∧ (Units.map gA.toMonoidHom).comp ψ = ψA ∧ (Units.map gB.toMonoidHom).comp ψ = ψB := by
  intro Γ O₀ A B _ _ _ _ _ _ _ _ _ _ fA fB _ hAi hB hBl ψA ψB hS
  have iA := IsFractionRing.injective A (FractionRing A)
  have iB := IsFractionRing.injective B (FractionRing B)
  letI : Algebra O₀ A := fA.toAlgebra
  letI : Algebra O₀ B := fB.toAlgebra
  let αA : MonoidAlgebra O₀ Γ →+* A :=
    (MonoidAlgebra.lift O₀ A Γ ((Units.coeHom A).comp ψA)).toRingHom
  let αB : MonoidAlgebra O₀ Γ →+* B :=
    (MonoidAlgebra.lift O₀ B Γ ((Units.coeHom B).comp ψB)).toRingHom
  have hker : ∀ F, αA F = 0 ↔ αB F = 0 := by
    intro F
    simp only [αA, αB, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_apply, Algebra.smul_def]
    exact hS _
  have aA : ∀ c, αA (algebraMap O₀ _ c) = fA c := fun c => AlgHom.commutes _ c
  have aB : ∀ c, αB (algebraMap O₀ _ c) = fB c := fun c => AlgHom.commutes _ c
  have oA : ∀ g, αA (MonoidAlgebra.of O₀ Γ g) = ψA g := fun g => MonoidAlgebra.lift_of _ g
  have oB : ∀ g, αB (MonoidAlgebra.of O₀ Γ g) = ψB g := fun g => MonoidAlgebra.lift_of _ g
  let R : Subring A := αA.range
  let q : MonoidAlgebra O₀ Γ →+* R := αA.rangeRestrict
  have hq : Function.Surjective q := αA.rangeRestrict_surjective
  let φ : R →+* B := q.liftOfSurjective hq ⟨αB, fun F hF =>
    (hker F).1 (congrArg Subtype.val (RingHom.mem_ker.1 hF))⟩
  have hφ : ∀ F, φ (q F) = αB F := fun F => RingHom.liftOfRightInverse_comp_apply _ _ _ _ F
  have φi : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨F, rfl⟩ := hq r
    exact Subtype.ext ((hker F).2 (by rw [← hφ, hr]))
  let K := FractionRing R
  let jA : K →+* FractionRing A := IsFractionRing.lift (g := (algebraMap A _).comp R.subtype)
    (iA.comp Subtype.val_injective)
  let jB : K →+* FractionRing B := IsFractionRing.lift (g := (algebraMap B _).comp φ)
    (iB.comp φi)
  let p : MonoidAlgebra O₀ Γ →+* K := (algebraMap R K).comp q
  have pA : ∀ F, jA (p F) = algebraMap A _ (αA F) := fun F => IsFractionRing.lift_algebraMap _ _
  have pB : ∀ F, jB (p F) = algebraMap B _ (αB F) := fun F => by
    rw [← hφ]; exact IsFractionRing.lift_algebraMap _ _
  obtain ⟨O₁, hD, f, gA, gB, hmem, hgA, hgB, gAi, gBi, lA, lB, cA, cB⟩ :=
    common_of_field fA fB hAi hB hBl (p.comp (algebraMap O₀ _)) jA jB
      (fun c => by rw [RingHom.comp_apply, pA, aA]) (fun c => by rw [RingHom.comp_apply, pB, aB])
  let p₁ : MonoidAlgebra O₀ Γ →+* O₁ := p.codRestrict O₁ (fun F => (hmem _).2 ⟨_, (pA F).symm⟩)
  let ψ : Γ →* O₁ˣ := (p₁.toMonoidHom.comp (MonoidAlgebra.of O₀ Γ)).toHomUnits
  refine ⟨O₁, inferInstance, inferInstance, hD, f, gA, gB, ψ, gAi, gBi, lA, lB, cA, cB, ?_, ?_⟩
  · ext g
    apply iA
    rw [← oA, ← pA]
    exact hgA _
  · ext g
    apply iB
    rw [← oB, ← pB]
    exact hgB _

end GlobalTheory.Proof.dvr_of_reflects_facts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionField
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRecip

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (M : ℕ) (f : T.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f) → ∀ ζ : Ω, IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T M f hM hf ζ hζ s d hsd γ γ' hc
  obtain ⟨N₀, hN₀, hrec⟩ := _root_.GlobalTheory.FN.reciprocity_large_level Ω ε T f
  set N := N₀ * M with hNdef
  have hN : 0 < N := Nat.mul_pos hN₀ hM
  obtain ⟨⟨d', hd'⟩, hu⟩ := _root_.GlobalTheory.ZetaExp.main Ω ε s N hN
  obtain ⟨u, hu1, -⟩ := hu d' hd'
  have hunit : IsUnit ((d' : ℤ) : ZMod N) := hu1 ▸ u.isUnit
  set ω := eOm ε (1 / (N : ℚ)) with hω
  have hωp : IsPrimitiveRoot ω N := (_root_.GlobalTheory.FNRoots.main Ω ε).2.2.2.2.1 N hN
  have hωM : IsPrimitiveRoot (ω ^ N₀) M := hωp.pow hN rfl
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨i, -, hi⟩ := hωM.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hsζ : s ζ = ζ ^ d' := by
    rw [← hi, map_pow, map_pow, hd', ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    ring_nf
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdd : (d : ZMod M) = d' := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := (hζ.zpow_eq_one_iff_dvd (d' - d)).1 (by
      rw [zpow_sub₀ hζ0, ← hsd, ← hsζ, div_self]; exact (map_ne_zero s).2 hζ0)
    exact this
  obtain ⟨hl1, hl2⟩ := _root_.GlobalTheory.FNCongLift.cong_lift M N d d' hN (Dvd.intro_left N₀ rfl) hdd hunit
  obtain ⟨γ'', hc'', hκ⟩ := hl1 γ γ' hc
  have hact := _root_.GlobalTheory.FN.frac_sl_right_action Ω ε T
  have hinv : ∀ δ' ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL δ') (T.gal s f) = T.gal s f := by
    intro δ' hδ'
    obtain ⟨δ, hδ, hcδ⟩ := hl2 δ' hδ'
    have := hrec N hN (Dvd.intro M rfl) s d' hd' δ δ' hcδ
    rw [hf δ hδ] at this
    exact this.symm
  rw [hrec N hN (Dvd.intro M rfl) s d' hd' γ γ'' hc'']
  have hγ' : γ' = (γ' * γ''⁻¹) * γ'' := by group
  rw [hγ', map_mul, hact.2, hinv _ hκ]

end GlobalTheory.FNRecip
end

