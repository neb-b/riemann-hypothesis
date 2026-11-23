module

public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

def OsgoodStatement : Prop :=
  ∀ (e : ℕ) (U : Set (Fin e → ℂ)) (f : (Fin e → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f U →
    AnalyticOnNhd ℂ f U

theorem osgood : OsgoodStatement := by
  intro e U f hU hf z₀ hz₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hs : 0 < r / 2 := half_pos hr
  have hcl : Metric.closedBall z₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hd : ∀ ζ ∈ Metric.closedBall z₀ (r / 2), DifferentiableAt ℂ f ζ :=
    fun ζ hζ => hf.differentiableAt (hU.mem_nhds (hcl hζ))
  set L := ReciprocityTheory.AnForm.Osgood.fctlCLM z₀ hs f hd
  have hg : AnalyticAt ℂ (fun z => ((2 * (Real.pi : ℂ) * Complex.I) ^ e)⁻¹ *
      L (ReciprocityTheory.AnForm.Osgood.kern z₀ (r / 2) z)) z₀ :=
    analyticAt_const.mul ((L.analyticAt _).comp (ReciprocityTheory.AnForm.Osgood.kern_analyticAt z₀ hs))
  refine hg.congr ?_
  filter_upwards [Metric.ball_mem_nhds z₀ hs] with z hz
  rw [ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hs hd hz]
  exact inv_mul_cancel_left₀ (pow_ne_zero _ Complex.two_pi_I_ne_zero) _

end ReciprocityTheory.ChartRestriction.G.Geo
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory

def pot {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (L : Fin e → HermLine ι) :
    Fin e → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => Real.log ((L j).h z)

def IsSectionOn {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) :
    Prop :=
  ∃ a : K → ℕ, (∀ k, A.a k = a k) ∧ IsMultiHomog s a ∧ s ∉ P

def GoodProjExistsStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ

def FibreFiniteStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → ∀ y, (fibre P Ψ y).Finite

def PtsIntegrableStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w)

def PtsIndepStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    IsSmoothHerm A → IsSectionOn P A s →
    ptsIntegralAt P Ψ (pot L) (logNorm A s) = ptsIntegralAt P Ψ' (pot L) (logNorm A s)

def DivSuppArithStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (A : HermLine ι) (s : MRing ι) (W : Ideal (MRing ι)),
    IsArithVar P (n + 1) → IsSectionOn P A s → W ∈ divSupp P s →
    (IsHorizontal W → IsArithVar W n) ∧
    (¬ IsHorizontal W → IsMultiProjPrime W ∧ (charOf W).Prime ∧
      ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞))

def SheetIndepStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    ∀ᵐ y, ∀ w γ γ', IsSheet P Ψ y w γ → IsSheet P Ψ y w γ' →
      logNorm A s (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
        logNorm A s (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y

def DegreeStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (p : ℕ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → p.Prime →
    ptsIntegral P (pot L) (fun _ => 1) =
      ∑ᶠ V ∈ divSupp P (C (p : ℤ)),
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum e V (fun j => (L j).a) : ℝ)

def StokesStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (B B' : HermLine ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B → IsSmoothHerm B' →
    B.a = 0 → B'.a = 0 →
    ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (fun z => Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (fun z => Real.log (B'.h z))

def ArithmeticPoincareLelongFormula : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (logNorm A s) =
      (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z))

def SectionSpaceSymmetry : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm A' →
    IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (logNorm A' s')) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) =
    (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s'}) W : ℝ) * ptsIntegral W (pot L) (logNorm A s)) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')

section Tests

abbrev PBlk (n : ℕ) : Unit → Type := fun _ => Fin n

def fsLine (n : ℕ) : HermLine (PBlk n) :=
  HermLine.ofMetrics (fun _ => fsMetric (ι := Fin n)) 1

abbrev Xc (n : ℕ) (i : Fin n) : MRing (PBlk n) := X ⟨(), i⟩

end Tests

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

