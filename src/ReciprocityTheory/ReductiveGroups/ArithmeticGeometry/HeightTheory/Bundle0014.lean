module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.SemistableReduction.Bundle0006
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0012

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraicIndependentScaledForms
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

theorem algebraicIndependent_scaledForms {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (y : Fin (N + 1) → Ω) (jc : Fin (N + 1)) (hy : y jc = 1)
    (J : Fin D → Fin N) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (y (jc.succAbove (J b))) = if a = b then 1 else 0)
    (ρ : Option (Fin D) → Fin (D + 2)) (hρ : Function.Injective ρ) :
    AlgebraicIndependent K (Sum.elim
      (fun p : Fin (D + 2) × Fin (N + 1) =>
        (X (some p) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω))
      (fun o : Option (Fin D) => X none * ∑ j, X (some (ρ o, j)) * C (y j))) := by
  classical
  refine algebraicIndependent_of_derivations _ (Sum.elim
    (fun o => (pderiv o :
      Derivation Ω (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)
        (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)).restrictScalars K)
    (fun a => coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a))) ?_
  intro c H
  have hZ : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    intro o; simp [pderiv_X]
  have hpn : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (X none * ∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) =
        ∑ j, X (some (ρ o, j)) * C (y j) := by
    intro o; rw [Derivation.leibniz, hZ, smul_zero, zero_add, pderiv_X]; simp
  have hcd : ∀ a o, coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a)
      (X none * ∑ j, X (some (ρ o, j)) * C (y j)) =
        X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j)) := by
    intro a o
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Derivation.leibniz, coeffDer_X, coeffDer_C, map_sum]
  let M : Matrix (Option (Fin D)) (Option (Fin D))
      (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) := fun r o =>
    match r with
    | none => ∑ j, X (some (ρ o, j)) * C (y j)
    | some a => X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j))
  have e1 : ∑ o, c (Sum.inr o) * ∑ j, (X (some (ρ o, j)) * C (y j) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    have := H (Sum.inl none)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, Derivation.coe_restrictScalars, hpn] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [pderiv_X]), zero_add] at this
  have e2 : ∀ a, ∑ o, c (Sum.inr o) * (X none * ∑ j, (X (some (ρ o, j)) * C (δ a (y j)) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)) = 0 := by
    intro a
    have := H (Sum.inr a)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, hcd] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [coeffDer_X]), zero_add] at this
  have hv : M.mulVec (fun o => c (Sum.inr o)) = 0 := by
    funext r
    cases r with
    | none =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e1]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
    | some a =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e2 a]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
  let pt : Option (Fin (D + 2) × Fin (N + 1)) → Ω := fun v =>
    match v with
    | none => 1
    | some q => ∑ o : Option (Fin D), if ρ o = q.1 then
        (match o with
          | none => if q.2 = jc then 1 else 0
          | some b => (if q.2 = jc then -y (jc.succAbove (J b)) else 0) +
              (if q.2 = jc.succAbove (J b) then 1 else 0))
        else 0
  have hpt0 : ∀ j, pt (some (ρ none, j)) = if j = jc then 1 else 0 := by
    intro j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single none]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hpt1 : ∀ b j, pt (some (ρ (some b), j)) = (if j = jc then -y (jc.succAbove (J b)) else 0) +
      (if j = jc.succAbove (J b) then 1 else 0) := by
    intro b j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single (some b)]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hptn : pt none = 1 := rfl
  have hne : ∀ b, jc.succAbove (J b) ≠ jc := fun b => Fin.succAbove_ne jc (J b)
  have hev : (MvPolynomial.eval pt).mapMatrix M = 1 := by
    ext r o
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    cases r with
    | none =>
      cases o with
      | none => simp [M, hpt0, hy]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, Matrix.one_apply]
    | some a =>
      cases o with
      | none =>
        simp [M, hpt0, hy, hptn, Matrix.one_apply]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, hδ, Matrix.one_apply, hptn]
  have hdet : M.det ≠ 0 := by
    intro h0
    have := RingHom.map_det (MvPolynomial.eval pt) M
    rw [h0, map_zero, hev, Matrix.det_one] at this
    exact zero_ne_one this
  have hc2 : ∀ o, c (Sum.inr o) = 0 := fun o =>
    congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hv) o
  intro i
  rcases i with p | o
  · have := H (Sum.inl (some p))
    simpa [Fintype.sum_sum_type, hc2, pderiv_X, Pi.single_apply] using this
  · exact hc2 o

theorem scalarRatio_self {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V}
    (hf : f ≠ 0) : ratio (Ω := Ω) f f = 1 := by
  unfold ratio
  split_ifs with h
  · have hc : f = h.choose • f := h.choose_spec
    have h0 : (h.choose - 1) • f = 0 := by
      rw [sub_smul, one_smul, ← hc, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hf
  · exact absurd ⟨1, (one_smul Ω f).symm⟩ h

theorem optionEquivLeft_rename_some' {R S : Type*} [CommRing R] (a : MvPolynomial S R) :
    MvPolynomial.optionEquivLeft R S (MvPolynomial.rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on
  next r => simp [MvPolynomial.optionEquivLeft_C]
  next p q hp hq => simp [hp, hq]
  next p s hp => simp [hp, MvPolynomial.optionEquivLeft_X_some]

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CoeffPsiPNeZero
section
namespace ReciprocityTheory.ChartRestriction.G.T0.WH

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p]

def wt (s : σ →₀ ℕ) : ℕ := ∑ v, if p v then s v else 0

theorem wt_add (s t : σ →₀ ℕ) : wt p (s + t) = wt p s + wt p t := by
  simp only [wt, Finsupp.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem wt_single (v : σ) (e : ℕ) : wt p (Finsupp.single v e) = if p v then e else 0 := by
  simp only [wt]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ v) h

noncomputable def psiP : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun v => if p v then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

theorem psiP_monomial (s : σ →₀ ℕ) (a : K) :
    psiP p (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ wt p s := by
  have key : ∀ v, (if p v then Polynomial.C (X v : MvPolynomial σ K) * Polynomial.X
      else Polynomial.C (X v)) ^ (s v)
      = Polynomial.C ((X v : MvPolynomial σ K) ^ s v) * Polynomial.X ^ (if p v then s v else 0) := by
    intro v
    split_ifs <;> simp [mul_pow]
  rw [psiP, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finset.prod_congr rfl (fun v _ => key v), Finset.prod_mul_distrib, ← map_prod,
    Finset.prod_pow_eq_pow_sum, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul, wt]
  ring

theorem psiP_eq_of_isWeightedHomogeneous (n : ℕ) (f : MvPolynomial σ K) (hf : ∀ s ∈ f.support, wt p s = n) :
    psiP p f = Polynomial.C f * Polynomial.X ^ n := by
  have h : ∀ s ∈ f.support, psiP p (monomial s (AddMonoidAlgebra.coeff f s))
      = Polynomial.C (monomial s (AddMonoidAlgebra.coeff f s)) * Polynomial.X ^ n := fun s hs => by
    rw [psiP_monomial, hf s hs]
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl h, ← Finset.sum_mul, ← map_sum, ← f.as_sum]

private theorem psiP_eq_sum_monomial (f : MvPolynomial σ K) :
    psiP p f = ∑ s ∈ f.support, Polynomial.C (monomial s (AddMonoidAlgebra.coeff f s)) * Polynomial.X ^ wt p s := by
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [psiP_monomial]

private theorem coeff_psiP (f : MvPolynomial σ K) (k : ℕ) :
    (psiP p f).coeff k = ∑ s ∈ f.support.filter (fun s => wt p s = k), monomial s (AddMonoidAlgebra.coeff f s) := by
  rw [psiP_eq_sum_monomial, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : wt p s = k
  · subst h
    simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

theorem coeff_psiP_ne_zero (f : MvPolynomial σ K) (s : σ →₀ ℕ) (hs : s ∈ f.support) :
    (psiP p f).coeff (wt p s) ≠ 0 := by
  intro h
  have h' := congrArg (AddMonoidAlgebra.coeff · s) h
  rw [coeff_psiP, MvPolynomial.coeff_sum, Finset.sum_eq_single s] at h'
  · classical
    simp only [coeff_monomial, ite_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h'
    exact (mem_support_iff.mp hs) h'
  · classical
    intro t _ hts
    rw [coeff_monomial, ite_eq_right hts]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨hs, rfl⟩)).elim

theorem hom_of_psiP (n : ℕ) (f : MvPolynomial σ K) (hf : psiP p f = Polynomial.C f * Polynomial.X ^ n) :
    ∀ s ∈ f.support, wt p s = n := by
  intro s hs
  by_contra hne
  apply coeff_psiP_ne_zero p f s hs
  rw [hf, Polynomial.coeff_C_mul_X_pow, ite_eq_right hne]

theorem hom_of_dvd (n : ℕ) (H A : MvPolynomial σ K) (hH0 : H ≠ 0)
    (hH : ∀ s ∈ H.support, wt p s = n) (hA : A ∣ H) : ∃ m, ∀ s ∈ A.support, wt p s = m := by
  obtain ⟨B, rfl⟩ := hA
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hH0
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hH0
  have hne : ∀ F : MvPolynomial σ K, F ≠ 0 → psiP p F ≠ 0 := by
    intro F hF h0
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hF
    exact coeff_psiP_ne_zero p F s (mem_support_iff.mpr hs) (by rw [h0, Polynomial.coeff_zero])
  have hprod : psiP p A * psiP p B = Polynomial.C (A * B) * Polynomial.X ^ n := by
    rw [← map_mul]
    exact psiP_eq_of_isWeightedHomogeneous p n _ hH
  have hd := congrArg Polynomial.natDegree hprod
  have ht := congrArg Polynomial.natTrailingDegree hprod
  rw [Polynomial.natDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.natDegree_C_mul_X_pow _ _ hH0] at hd
  rw [Polynomial.natTrailingDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hH0] at ht
  have h1 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p A)
  have h2 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p B)
  refine ⟨(psiP p A).natDegree, fun s hs => ?_⟩
  have hc := coeff_psiP_ne_zero p A s hs
  have h3 := Polynomial.le_natDegree_of_ne_zero hc
  have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
  omega

end ReciprocityTheory.ChartRestriction.G.T0.WH
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FracFieldPositiveRowsOmega
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

abbrev PolyRingPositiveRowsBase : Type := MvPolynomial {v : TVar d.D d.N // v.1 ≠ 0} K

abbrev PolyRingPositiveRowsOmega (c : ι) : Type := MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c)

abbrev FracFieldPositiveRowsBase : Type := FractionRing d.PolyRingPositiveRowsBase

abbrev FracFieldPositiveRowsOmega (c : ι) : Type := FractionRing (d.PolyRingPositiveRowsOmega c)

noncomputable def eLX4 : KTf K d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase) :=
  letI := (FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsBase) (σ := Fin (d.N + 1))
  IsFractionRing.ringEquivOfRingEquiv (FractionFieldVariableLift.hL K d.D d.N)

noncomputable def eEX4 (c : ι) : OmS (Ω c) d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) :=
  letI := (FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsOmega c) (σ := Fin (d.N + 1))
  IsFractionRing.ringEquivOfRingEquiv (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c))

theorem eLX4_algebraMap (P : KTp K d.D d.N) :
    d.eLX4 (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P) =
      FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1)) (FractionFieldVariableLift.hL K d.D d.N P) := by
  letI := (FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsBase) (σ := Fin (d.N + 1))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (FractionFieldVariableLift.hL K d.D d.N) P

theorem eEX4_algebraMap (c : ι) (P : MvPolynomial (SVar d.D d.N) (Ω c)) :
    d.eEX4 c (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) P) =
      FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1)) (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c) P) := by
  letI := (FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsOmega c) (σ := Fin (d.N + 1))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c)) P

noncomputable def psiE (c : ι) : d.PolyRingPositiveRowsBase →+* d.FracFieldPositiveRowsOmega c :=
  (algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c)).comp (d.offBaseSubstitution c).toRingHom

private theorem sumRingEquiv_X_inl' (R S₁ S₂ : Type) [CommSemiring R] (b : S₁) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
  MvPolynomial.sumRingEquiv_X_inl R S₁ S₂ b

private theorem sumRingEquiv_X_inr' (R S₁ S₂ : Type) [CommSemiring R] (q : S₂) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.X (Sum.inr q)) =
      MvPolynomial.C (MvPolynomial.X q) :=
  MvPolynomial.sumRingEquiv_X_inr R S₁ S₂ q

private theorem sumRingEquiv_C' (R S₁ S₂ : Type) [CommSemiring R] (a : R) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) :=
  MvPolynomial.sumRingEquiv_C R S₁ S₂ a

theorem compat0 (c : ι) (P : KTp K d.D d.N) :
    d.eEX4 c (d.sH c P) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) _
      (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N P)) := by
  have hXlE : ∀ b, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
    fun b => sumRingEquiv_X_inl' _ _ _ b
  have hXrE : ∀ q, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.X (Sum.inr q)) = MvPolynomial.C (MvPolynomial.X q) :=
    fun q => sumRingEquiv_X_inr' _ _ _ q
  have hCE : ∀ b, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.C b) = MvPolynomial.C (MvPolynomial.C b) :=
    fun b => sumRingEquiv_C' _ _ _ b
  have hXlL : ∀ b, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
    fun b => sumRingEquiv_X_inl' _ _ _ b
  have hXrL : ∀ q, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.X (Sum.inr q)) = MvPolynomial.C (MvPolynomial.X q) :=
    fun q => sumRingEquiv_X_inr' _ _ _ q
  have hCL : ∀ b, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.C b) = MvPolynomial.C (MvPolynomial.C b) :=
    fun b => sumRingEquiv_C' _ _ _ b
  have hEX : ∀ p, FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c) p =
      MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.rename (FractionFieldVariableLift.eS d.D d.N (d.jc c)) p) := fun p => rfl
  have hLX : ∀ p, FractionFieldVariableLift.hL K d.D d.N p =
      MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.rename (FractionFieldVariableLift.eT d.D d.N) p) := fun p => rfl
  have sac1 : ∀ {β : Type} (y : β) (p : Fin d.N → β),
      Fin.succAboveCases (α := fun _ => β) (d.jc c) y p (d.jc c) = y :=
    fun y p => Fin.insertNth_apply_same (α := fun _ => _) _ y p
  have sac2 : ∀ {β : Type} (y : β) (p : Fin d.N → β) (k : Fin d.N),
      Fin.succAboveCases (α := fun _ => β) (d.jc c) y p ((d.jc c).succAbove k) = p k :=
    fun y p k => Fin.insertNth_apply_succAbove (α := fun _ => _) _ y p k
  have hpsiC : ∀ a, d.offBaseSubstitution c (MvPolynomial.C a) = MvPolynomial.C (algebraMap K (Ω c) a) := by
    intro a
    rw [← MvPolynomial.algebraMap_eq (R := K), AlgHom.commutes, MvPolynomial.algebraMap_apply]
  have hpsiX : ∀ v, d.offBaseSubstitution c (MvPolynomial.X v) =
      Fin.succAboveCases (α := fun _ => MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c))
        (d.jc c) (-∑ k, MvPolynomial.X (⟨v.1.1, v.2⟩, k) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (⟨v.1.1, v.2⟩, k)) v.1.2 := by
    intro v
    simp only [Data.offBaseSubstitution, MvPolynomial.aeval_X]
  have hpsi (p : d.PolyRingPositiveRowsBase) :
      d.psiE c p = algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c)
        (d.offBaseSubstitution c p) := rfl
  have e1 : ∀ a, d.sH c (MvPolynomial.C a) = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N) (MvPolynomial.C (algebraMap K (Ω c) a)) := by
    intro a
    rw [← MvPolynomial.algebraMap_eq (R := K), AlgHom.commutes, ← MvPolynomial.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have e2 : ∀ p, d.sH c (MvPolynomial.X p) = sImg (d.jc c) (d.x c) p := by
    intro p
    simp only [Data.sH, sHom, MvPolynomial.aeval_X]
  have key : (d.eEX4 c).toRingHom.comp (d.sH c).toRingHom =
      (algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))).comp
        ((MvPolynomial.map (d.psiE c)).comp (FractionFieldVariableLift.hL K d.D d.N).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show d.eEX4 c (d.sH c (MvPolynomial.C a)) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))
        (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N (MvPolynomial.C a)))
      simp [e1, d.eEX4_algebraMap, hEX, hLX, hCE, hCL, FractionFieldVariableLift.toFracY, hpsi, hpsiC]
    · rintro ⟨i, j⟩
      show d.eEX4 c (d.sH c (MvPolynomial.X (i, j))) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))
        (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N (MvPolynomial.X (i, j))))
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [e2, sImg, sac1, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL, hCE,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY]
        · set_option synthInstance.maxHeartbeats 100000 in
          simp [e2, sImg, sac1, hi, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL, hCE,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY, hpsi, hpsiX, hpsiC]
      · by_cases hi : i = 0
        · subst hi
          simp [e2, sImg, sac2, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY]
        · simp [e2, sImg, sac2, hi, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY, hpsi, hpsiX]
  exact RingHom.congr_fun key P

theorem psiE_injective (h : d.S1) (c : ι) : Function.Injective (d.psiE c) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  have e := d.compat0 c ((FractionFieldVariableLift.hL K d.D d.N).symm (MvPolynomial.C p))
  rw [RingEquiv.apply_symm_apply, MvPolynomial.map_C, hp, map_zero, map_zero] at e
  have e2 := (RingEquiv.map_eq_zero_iff (d.eEX4 c)).mp e
  have e3 := h c (e2.trans (map_zero (d.sH c)).symm)
  have e4 : (MvPolynomial.C p : MvPolynomial (Fin (d.N + 1)) d.PolyRingPositiveRowsBase) = 0 := by
    rw [← RingEquiv.apply_symm_apply (FractionFieldVariableLift.hL K d.D d.N) (MvPolynomial.C p), e3, map_zero]
  exact MvPolynomial.C_eq_zero.mp e4

noncomputable def algLE (h : d.S1) (c : ι) : Algebra d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) :=
  (IsFractionRing.lift (A := d.PolyRingPositiveRowsBase) (K := d.FracFieldPositiveRowsBase) (d.psiE_injective h c)).toAlgebra

theorem algLE_algebraMap (h : d.S1) (c : ι) (p : d.PolyRingPositiveRowsBase) :
    letI := d.algLE h c;
    algebraMap d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) (algebraMap d.PolyRingPositiveRowsBase d.FracFieldPositiveRowsBase p) = d.psiE c p := IsFractionRing.lift_algebraMap (d.psiE_injective h c) p

theorem fieldEquiv_compat_liftY (h : d.S1) (c : ι) (q : KTf K d.D d.N) :
    letI := d.algLE h c;
    d.eEX4 c (d.KTtoS h c q) = VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1)) (d.eLX4 q) := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := KTp K d.D d.N) q
  simp only [map_div₀]
  congr 1
  all_goals
    rw [show ∀ P : KTp K d.D d.N, d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P) =
      d.sH c P from fun P => IsFractionRing.lift_algebraMap _ _]
    rw [d.compat0 c, d.eLX4_algebraMap]
    unfold FractionFieldVariableLift.toFracY VariableBasisExtension.liftY
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap, RingHom.comp_apply, MvPolynomial.map_map]
    rw [show (@algebraMap d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) _ _ (d.algLE h c)).comp (algebraMap d.PolyRingPositiveRowsBase d.FracFieldPositiveRowsBase) =
      d.psiE c from RingHom.ext fun p => d.algLE_algebraMap h c p]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def fDivE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N :=
  ∏ c, ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p

noncomputable def omE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N := d.De hd h * d.fDivE hd h ^ 2

def IsPres (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) : Prop :=
  b ≠ 0 ∧ algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a =
    d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ∧
  ∃ m : Fin (d.D + 1) → ℕ, m 0 = 0 ∧ ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m a ∧
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m b

noncomputable def mSgP (sg : K →+* ℂ) (a b : KTp K d.D d.N) : ℝ :=
  ∫ z, (Real.log ‖d.evT sg 0 (d.tOf z) a‖ - Real.log ‖d.evT sg 0 (d.tOf z) b‖)
    ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

