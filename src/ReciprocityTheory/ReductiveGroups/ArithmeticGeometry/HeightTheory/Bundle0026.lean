module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FZMultiHomogeneousDegreeSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DegreeSumIdentity
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

theorem DegreeSumIdentity (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c := by
  exact d.fZ_multiHomogeneous_degree_sum hd h c F hF

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SpecialFibreFactorization
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

theorem SpecialFibreFactorization (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (x : Fin (d.N + 1) → K) (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
        (MvPolynomial.aeval (fun v : TVar d.D d.N =>
          if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
      algebraMap K (KTf K d.D d.N) κ *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p := by
  classical
  obtain ⟨P, Q, hQ0, hQx, hPQ, hspec⟩ := d.norm_generic_ratio_spec hd h c
  obtain ⟨Pp, Pm, hPm0, hPpx, hPmx, hPi⟩ := d.pi_free hd h c (d.w (d.jc c) c)
  obtain ⟨κ, hκ, hκeq⟩ := d.norm_ratio_pi hd h c x hx
  refine ⟨κ, hκ, ?_⟩
  have hφinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hpoly : Q * F * Pm = P * Pp := by
    apply hφinj
    simp only [map_mul]
    rw [hF, hPi, hPQ]
    simp only [fZ]
    ring
  have hsub := congrArg (d.sub0 x) hpoly
  simp only [map_mul, hQx, hPmx, hPpx] at hsub
  have hφ := congrArg (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)) hsub
  simp only [map_mul] at hφ
  rw [hspec x hx, hPi] at hφ
  have hQ' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q ≠ 0 :=
    (map_ne_zero_iff _ hφinj).mpr hQ0
  have hPm' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm ≠ 0 :=
    (map_ne_zero_iff _ hφinj).mpr hPm0
  rw [← hκeq]
  apply mul_left_cancel₀ (mul_ne_zero hQ' hPm')
  calc _ = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x F) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm := by ring
    _ = _ := hφ
    _ = _ := by ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SphereMeanSubArchimedean
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem eval_indep_of_first_block (q : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (hq : IsMultiHomogeneous m q) (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ)
    (t : Fin d.D → Fin (d.N + 1) → ℂ) : d.evT sg t0 t q = d.evT sg 0 t q := by
  unfold evT
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  apply Finset.prod_congr rfl
  rintro ⟨b, j⟩ _
  have hsum : ∑ j : Fin (d.N + 1), s (0, j) = 0 := by
    rw [hq s hs 0, hm0]
  cases b using Fin.cases with
  | zero =>
    have h0 : s (0, j) = 0 := (Finset.sum_eq_zero_iff.mp hsum) j (Finset.mem_univ _)
    simp [h0]
  | succ i => rfl

theorem sphereMean_sub_archimedean (a b : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hma : IsMultiHomogeneous m a) (hmb : IsMultiHomogeneous m b)
    (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg a) -
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg b) = d.mSgP sg a b := by
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  have hmp := hint_mpTail d.D (d.N + 1) hn
  have key : ∀ q : KTp K d.D d.N, q ≠ 0 → IsMultiHomogeneous m q →
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg q) =
        ∫ w, Real.log ‖d.evT sg 0 (d.tOf w) q‖ ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) ∧
      Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
    intro q hq0 hq
    have hq0' : MvPolynomial.map sg q ≠ 0 := fun h =>
      hq0 (MvPolynomial.map_injective _ sg.injective (by rw [h, map_zero]))
    have hq' : IsMultiHomogeneous m (MvPolynomial.map sg q) :=
      fun s hs => hq s (MvPolynomial.support_map_subset _ _ hs)
    have hI := hint_logInt_tail hn hq0' hq' hm0 0
    have heq : ∀ w, d.evT sg 0 (d.tOf w) q =
        MvPolynomial.eval (hintPt 0 w) (MvPolynomial.map sg q) := by
      intro w
      rw [MvPolynomial.eval_map]
      rfl
    have hI' : Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
      simp only [heq]
      exact hI
    refine ⟨?_, hI'⟩
    have hpt : ∀ z : ReciprocityTheory.MultiplicativeHeights.BlockSphere (d.D + 1) (d.N + 1),
        Real.log ‖MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q)‖ =
          Real.log ‖d.evT sg 0 (d.tOf (fun i : Fin d.D => z i.succ)) q‖ := by
      intro z
      have h1 : MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q) =
          d.evT sg (fun j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z 0) j)
            (d.tOf (fun i : Fin d.D => z i.succ)) q := by
        rw [MvPolynomial.eval_map]
        unfold evT
        congr 1
        funext v
        rcases v with ⟨b, j⟩
        cases b using Fin.cases with
        | zero => rfl
        | succ i => rfl
      rw [h1, d.eval_indep_of_first_block q m hm0 hq sg]
    unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp only [hpt]
    have h2 := MeasureTheory.integral_map (μ := ReciprocityTheory.MultiplicativeHeights.blockSphereProb (d.D + 1) (d.N + 1))
      hmp.measurable.aemeasurable (f := fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
      (by rw [hmp.map_eq]; exact hI'.aestronglyMeasurable)
    rw [hmp.map_eq] at h2
    exact h2.symm
  obtain ⟨ha1, ha2⟩ := key a ha hma
  obtain ⟨hb1, hb2⟩ := key b hb hmb
  rw [ha1, hb1, ← integral_sub ha2 hb2]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

