module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatioLemmas
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def chartHomogQ (c : (k : ι) → Fin (n k + 1)) (f : MvPolynomial (Coord n) ℚ)
    [Fintype ι] : MvPolynomial (Coord n) ℚ :=
  ∑ m ∈ f.support, C (AddMonoidAlgebra.coeff f m) * ∏ p : Coord n, (X p ^ m p * X ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p))

theorem le_totalDegree_of_mem_support {f : MvPolynomial (Coord n) ℚ} {m : Coord n →₀ ℕ}
    (hm : m ∈ f.support) (p : Coord n) : m p ≤ f.totalDegree :=
  (monomial_le_degreeOf p hm).trans (degreeOf_le_totalDegree f p)

variable [Fintype ι]

theorem aeval_chartHomogQ {S : Type*} [CommRing S] [Algebra ℚ S] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → S) :
    aeval y (chartHomogQ c f) = ∑ m ∈ f.support, algebraMap ℚ S (AddMonoidAlgebra.coeff f m) *
      ∏ p : Coord n, (y p ^ m p * y ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [chartHomogQ, map_sum, map_prod]

theorem aeval_chartHomogQ_field {K : Type*} [Field K] [Algebra ℚ K] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → K) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    aeval y (chartHomogQ c f) = (∏ p : Coord n, y ⟨p.1, c p.1⟩ ^ f.totalDegree) *
      aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) f := by
  rw [aeval_chartHomogQ, aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h : ∀ p : Coord n, y p ^ m p * y ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p) =
      y ⟨p.1, c p.1⟩ ^ f.totalDegree * (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    intro p
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (le_totalDegree_of_mem_support hm p)
    have hyp := hy p.1
    rw [he, Nat.add_sub_cancel_left, pow_add, div_pow]
    field_simp
  simp_rw [h, Finset.prod_mul_distrib]
  ring

theorem coneMapQ_chartHomogQ (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) :
    OrbitCurve.coneMapQ x (chartHomogQ c f) =
      C (aeval (flatCone x) (chartHomogQ c f)) * ∏ p : Coord n, X p.1 ^ f.totalDegree := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [OrbitCurve.coneMapQ, aeval_chartHomogQ, aeval_chartHomogQ, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h : ∀ p : Coord n,
      (C (flatCone x p) * X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) ^ m p *
        (C (flatCone x ⟨p.1, c p.1⟩) * X p.1) ^ (f.totalDegree - m p) =
      C (flatCone x p ^ m p * flatCone x ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p)) *
        X p.1 ^ f.totalDegree := by
    intro p
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (le_totalDegree_of_mem_support hm p)
    rw [he, Nat.add_sub_cancel_left]
    simp only [mul_pow, map_mul, map_pow, pow_add]
    ring
  simp only [h, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.algebraMap_apply]
  ring

theorem aeval_ratio_eq_zero (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ} (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x))
    (hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0) (f : MvPolynomial (Coord n) ℚ)
    (hf : aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0) :
    aeval (fun p ↦ z p / z ⟨p.1, c p.1⟩) f = 0 := by
  have hx : aeval (flatCone x) (chartHomogQ c f) = 0 := by
    rw [aeval_chartHomogQ_field c f (flatCone x) hc]
    exact mul_eq_zero_of_right _ hf
  have hker : chartHomogQ c f ∈ RingHom.ker (OrbitCurve.coneMapQ x) := by
    rw [RingHom.mem_ker, coneMapQ_chartHomogQ, hx, map_zero, zero_mul]
  classical
  rw [OrbitCurve.ker_coneMapQ] at hker
  have hle : ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) ≤
      RingHom.ker (aeval z : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ) := by
    refine Ideal.map_le_iff_le_comap.mpr fun g hg ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_def,
      algebraMap_int_eq, ← eval_map]
    exact hz.2 g hg
  have h := hle hker
  rw [RingHom.mem_ker, aeval_chartHomogQ_field c f z hz0] at h
  exact (mul_eq_zero.mp h).resolve_left
    (Finset.prod_ne_zero_iff.mpr fun p _ ↦ pow_ne_zero _ (hz0 p.1))

variable [DecidableEq ι]

theorem chart_ne_zero_of_mem_mcPts (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) (k : ι) : z ⟨k, c k⟩ ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := hz.1 k
  obtain ⟨g, hg0, hg⟩ := exists_int_relation (flatCone x ⟨k, i⟩ / flatCone x ⟨k, c k⟩)
  have h := hz.2 _ (homogForm_mem_orbitIdeal x g ⟨k, i⟩ ⟨k, c k⟩ rfl (hc k) hg)
  rw [eval_homogForm, h0, homog_sum_zero] at h
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg0))
    (pow_ne_zero _ hi) h

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G MeasureTheory

namespace PtsIntegralPoints

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem rel_equivalence (P : Ideal (Geo.MRing ι)) :
    Equivalence (fun z z' : Geo.mcPts P ↦
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p) := by
  constructor
  · intro z
    exact ⟨fun _ ↦ 1, fun _ ↦ one_ne_zero, by funext p; simp⟩
  · rintro z z' ⟨c, hc, h⟩
    refine ⟨fun k ↦ (c k)⁻¹, fun k ↦ inv_ne_zero (hc k), ?_⟩
    funext p
    rw [h]
    exact (inv_mul_cancel_left₀ (hc p.1) _).symm
  · rintro z z' z'' ⟨c, hc, h⟩ ⟨d, hd, h'⟩
    refine ⟨fun k ↦ d k * c k, fun k ↦ mul_ne_zero (hd k) (hc k), ?_⟩
    funext p
    rw [h', h, mul_assoc]

theorem segre_ne_zero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : Geo.segre z ≠ 0 := by
  choose i hi using hz
  intro h
  have := congrFun h i
  simp only [Geo.segre, Pi.zero_apply] at this
  exact Finset.prod_ne_zero_iff.mpr (fun k _ ↦ hi k) this

theorem sheetDensity_eq (P : Ideal (Geo.MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z)
    (y : Fin 0 → ℂ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ Geo.mcPts P)
    (hΨ : Ψ (Geo.segre z) = Fin.cons 1 y) :
    Geo.sheetDensity P Ψ Fin.elim0 g y (Geo.segre z) = g z := by
  have hex : ∃ γ, Geo.IsSheet P Ψ y (Geo.segre z) γ := by
    refine ⟨fun _ ↦ z, rfl, Filter.Eventually.of_forall fun y' ↦ ⟨differentiableAt_const _, hz, ?_⟩⟩
    rw [Subsingleton.elim y' y]
    exact hΨ
  rw [Geo.sheetDensity, dite_eq_left hex]
  obtain ⟨hseg, hev⟩ := hex.choose_spec
  have hmem : hex.choose y ∈ Geo.mcPts P := hev.self_of_nhds.2.1
  obtain ⟨c, hc, hcz⟩ := Geo.sameOrbit_of_segre (z := z) hmem.1 1 one_ne_zero (by rw [one_smul, hseg])
  have hgz : g z = g (hex.choose y) := (congrArg g hcz).trans (hg c _ hc hmem)
  rw [hgz]
  simp [Geo.maDensity, Geo.mixedDisc]

theorem ptsIntegralAt_eq [Nonempty K] (P : Ideal (Geo.MRing ι)) (hP : Geo.IsMultiHomogIdeal P)
    (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (hΨ : Geo.IsGoodProj P Ψ) :
    Geo.ptsIntegralAt P Ψ Fin.elim0 g = ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P) := by
  classical
  have hE := rel_equivalence P
  have hcons : ∀ (y : Fin 0 → ℂ) (v : Fin (0 + 1) → ℂ), v = Fin.cons 1 y ↔ v 0 = 1 := by
    intro y v
    constructor
    · rintro rfl; rfl
    · intro h; funext i; rw [show i = 0 from Fin.ext (by have := i.isLt; omega)]; exact h
  have hne : ∀ z ∈ Geo.mcPts P, Ψ (Geo.segre z) 0 ≠ 0 := fun z hz h ↦
    hΨ z hz (funext fun i ↦ by rw [show i = 0 from Fin.ext (by have := i.isLt; omega)]; exact h)
  let k₀ : K := Classical.arbitrary K
  let t : projPts P → ℂ := fun q ↦ (Ψ (Geo.segre (Quot.out q : Geo.mcPts P)) 0)⁻¹
  have ht : ∀ q, t q ≠ 0 := fun q ↦ inv_ne_zero (hne _ (Quot.out q).2)
  let c : projPts P → K → ℂ := fun q k ↦ if k = k₀ then t q else 1
  have hc : ∀ q k, c q k ≠ 0 := fun q k ↦ by
    simp only [c]
    split_ifs
    · exact ht q
    · exact one_ne_zero
  have hcprod : ∀ q, ∏ k, c q k = t q := fun q ↦ by simp [c]
  let zq : projPts P → (Σ k, ι k) → ℂ := fun q p ↦ c q p.1 * (Quot.out q).1 p
  have hzq : ∀ q, zq q ∈ Geo.mcPts P := fun q ↦ Geo.mcPts_smul hP (c q) (hc q) (Quot.out q).2
  have hseg : ∀ q, Geo.segre (zq q) = t q • Geo.segre (Quot.out q : Geo.mcPts P) := fun q ↦ by
    rw [← hcprod q]
    exact Geo.segre_smul (c q) (Quot.out q).1
  have hone : ∀ q, Ψ (Geo.segre (zq q)) 0 = 1 := fun q ↦ by
    rw [hseg, map_smul, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ (hne _ (Quot.out q).2)
  have hrep : ∀ z : Geo.mcPts P, ∃ d : K → ℂ, (∀ k, d k ≠ 0) ∧
      (z : (Σ k, ι k) → ℂ) = fun p ↦ d p.1 * (Quot.out (Quot.mk _ z : projPts P)).1 p :=
    fun z ↦ hE.eqvGen_iff.mp (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ z : projPts P)))
  have hsum : ∀ y : Fin 0 → ℂ, ∑ᶠ w ∈ Geo.fibre P Ψ y, Geo.sheetDensity P Ψ Fin.elim0 g y w =
      ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P) := by
    intro y
    let σ : projPts P → Geo.fibre P Ψ y := fun q ↦
      ⟨Geo.segre (zq q), zq q, hzq q, rfl, (hcons y _).mpr (hone q)⟩
    have hinj : Function.Injective σ := by
      intro q q' h
      have h' : Geo.segre (zq q) = Geo.segre (zq q') := congrArg Subtype.val h
      obtain ⟨d, hd, hdq⟩ :=
        Geo.sameOrbit_of_segre (z := zq q) (hzq q').1 1 one_ne_zero (by rw [one_smul, h'])
      have e1 : (Quot.mk _ (Quot.out q) : projPts P) = Quot.mk _ ⟨zq q, hzq q⟩ :=
        Quot.sound ⟨c q, hc q, rfl⟩
      have e2 : (Quot.mk _ ⟨zq q', hzq q'⟩ : projPts P) = Quot.mk _ ⟨zq q, hzq q⟩ :=
        Quot.sound ⟨d, hd, hdq⟩
      have e3 : (Quot.mk _ (Quot.out q') : projPts P) = Quot.mk _ ⟨zq q', hzq q'⟩ :=
        Quot.sound ⟨c q', hc q', rfl⟩
      rw [Quot.out_eq] at e1 e3
      exact e1.trans (e2.symm.trans e3.symm)
    have hsurj : Function.Surjective σ := by
      rintro ⟨w, z, hz, rfl, hw⟩
      obtain ⟨d, hd, hdz⟩ := hrep ⟨z, hz⟩
      refine ⟨Quot.mk _ ⟨z, hz⟩, Subtype.ext ?_⟩
      have hsz : Geo.segre z = (∏ k, d k) •
          Geo.segre (Quot.out (Quot.mk _ ⟨z, hz⟩ : projPts P) : Geo.mcPts P) := by
        rw [← Geo.segre_smul]
        exact congrArg Geo.segre hdz
      have h1 := (hcons y _).mp hw
      rw [hsz, map_smul, Pi.smul_apply, smul_eq_mul] at h1
      have h2 : ∏ k, d k = t (Quot.mk _ ⟨z, hz⟩) := eq_inv_of_mul_eq_one_left h1
      show Geo.segre (zq _) = Geo.segre z
      rw [hseg, hsz, h2]
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv (Equiv.ofBijective σ ⟨hinj, hsurj⟩)]
    refine finsum_congr fun q ↦ ?_
    show Geo.sheetDensity P Ψ Fin.elim0 g y (Geo.segre (zq q)) = _
    rw [sheetDensity_eq P Ψ g hg y (hzq q) ((hcons y _).mpr (hone q))]
    exact hg (c q) _ (hc q) (Quot.out q).2
  rw [Geo.ptsIntegralAt]
  simp only [hsum]
  rw [integral_const, MeasureTheory.volume_pi, Measure.pi_of_empty]
  simp

theorem exists_isGoodProj (P : Ideal (Geo.MRing ι)) (hfin : Finite (projPts P)) :
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), Geo.IsGoodProj P Ψ := by
  have hE := rel_equivalence P
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ) (M := ((k : K) → ι k) → ℂ)
    (fun q : projPts P ↦ Geo.segre (Quot.out q).1)
    (fun q ↦ segre_ne_zero (z := (Quot.out q).1) (Quot.out q).2.1)
  refine ⟨LinearMap.pi fun _ ↦ f, fun z hz h ↦ ?_⟩
  obtain ⟨d, hd, hdz⟩ := hE.eqvGen_iff.mp (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ ⟨z, hz⟩ : projPts P)))
  have h0 : f (Geo.segre z) = 0 := congrFun h 0
  have hsz : Geo.segre z = (∏ k, d k) •
      Geo.segre (Quot.out (Quot.mk _ ⟨z, hz⟩ : projPts P) : Geo.mcPts P) := by
    rw [← Geo.segre_smul]
    exact congrArg Geo.segre hdz
  rw [hsz, map_smul, smul_eq_mul] at h0
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hd k) (hf _) h0

def HomogStatement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) (g : ((Σ k, ι k) → ℂ) → ℝ),
    Geo.IsMultiHomogIdeal P → Finite (projPts P) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z) →
    Geo.ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) g =
      ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P)

theorem homogProof : HomogStatement := by
  intro K _ _ ι _ P g hP hfin hg
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), Geo.IsGoodProj P Ψ :=
    exists_isGoodProj P hfin
  rw [Geo.ptsIntegral, dite_eq_left hex]
  exact ptsIntegralAt_eq P hP g hg _ hex.choose_spec

section Dependence

open MvPolynomial

end Dependence

end PtsIntegralPoints

end GroundTheory.Heights₂.Heights
end

