module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.BqOriginSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

def BqOriginSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (a : 𝓞 E)
      (wLa : ExpGC.AdTy Xo a), ExpGD.AdRel C a wLa → ∀ (wLb : ExpGC.AdTy Xo (H.bar a)), ExpGD.AdRel C (H.bar a) wLb →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (overAt y.x S).left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J →
        val (ExpGC.Bq C.wP a wLa wLb) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J *
          val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J ^ (3 : ℤ) = 1

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPointStatement
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def ETSpanStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite ℤ Y] (R' : ℕ), 2 ≤ R' → ∀ (r : ℕ) (y z : Fin r → Y),
    (∀ a : Y, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : Y, a = u + R' • t) →
    ∀ a : Y, ∃ n : ℕ, 0 < n ∧
      n • a ∈ Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramFormPhiStatement
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

def GramFormPhiStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (β : SymB cj Y),
      (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b i) (b j)).PosDef) →
      ∃ b : Module.Basis (Fin (Module.finrank ℤ Y)) ℤ Y,
        (∀ j, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b j) (b j) / 2 ≤
          (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
              (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 3 * phiC cj β) ∧
        ∀ j (z : Y), |(β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b j) z| ≤
          2 * Real.sqrt (Module.finrank ℤ Y) * ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) z z / 2)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet

variable {S : Type} [CommRing S] {κ κ' κ'' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype κ''] [DecidableEq κ'']

theorem psJet_coe (m : ℕ) (P : MvPolynomial κ S) : psJet m (P : MvPowerSeries κ S) = Ideal.Quotient.mk _ P := by
  unfold psJet
  rw [psTrunc_eq]
  exact mk_trunc_coe m P

theorem jetSubstPS_X (m : ℕ) (P : κ → MvPowerSeries κ' S) (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (i : κ) : jetSubstPS (m := m) P (Ideal.Quotient.mk _ (X i)) = psJet m (P i) := by
  unfold jetSubstPS
  rw [jetMap_mk, MvPolynomial.aeval_X, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.cc_psTrunc', hP i, map_zero, sub_zero]
  rfl

theorem jetSubstPS_eq_jetMap (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    jetSubstPS (m := m) Q = jetMap (fun i => psTrunc m (Q i)) (fun i => psTrunc_mem_orig m (Q i) (hQ i)) := by
  unfold jetSubstPS
  congr 1
  funext i
  have h0 : MvPolynomial.constantCoeff (psTrunc m (Q i)) = 0 := by
    have hmem : (0 : κ' →₀ ℕ) ∈ degLE (ι := κ') m := by
      simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨fun _ => 0, ?_⟩, ?_⟩
      · ext j
        simp
      · simp
    rw [← hQ i]
    change AddMonoidAlgebra.coeff (psTrunc m (Q i)) 0 = _
    unfold psTrunc
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    rw [if_pos hmem]
    rfl
  rw [h0, map_zero, sub_zero]

theorem jetSubstPS_psJet (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ S) : jetSubstPS (m := m) Q (psJet m f) = psJet m (MvPowerSeries.subst Q f) := by
  rw [jetSubstPS_eq_jetMap m Q hQ, psJet_subst m Q hQ f]

theorem const_substPS (Q : κ' → MvPowerSeries κ'' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ' S) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst Q f) = 0 := by
  exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ) hQ hf

theorem jetSubstPS_comp (m : ℕ) (P : κ → MvPowerSeries κ' S) (Q : κ' → MvPowerSeries κ'' S)
    (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    (jetSubstPS (m := m) Q).comp (jetSubstPS (m := m) P) =
      jetSubstPS (m := m) (fun i => MvPowerSeries.subst Q (P i)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m P hP i, jetSubstPS_psJet m Q hQ,
    jetSubstPS_X m _ (fun i => const_substPS Q hQ (P i) (hP i)) i]

theorem jetSubstP_eq_jetSubstPS (m : ℕ) (σ : κ → MvPolynomial κ' S) (hσ : ∀ i, MvPolynomial.constantCoeff (σ i) = 0) :
    jetSubstP m σ = jetSubstPS (m := m) (fun i => (σ i : MvPowerSeries κ' S)) := by
  have hσ' : ∀ i, MvPowerSeries.constantCoeff ((σ i : MvPowerSeries κ' S)) = 0 := fun i => by
    show MvPowerSeries.coeff (0 : κ' →₀ ℕ) ((σ i : MvPowerSeries κ' S)) = 0
    rw [MvPolynomial.coeff_coe]
    exact hσ i
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m _ hσ' i, psJet_coe]
  unfold jetSubstP
  rw [jetMap_mk, MvPolynomial.aeval_X, hσ i, map_zero, sub_zero]

theorem jetCopy_eq_PS {d n : ℕ} (m : ℕ) (i : Fin n) :
    jetCopy (S := S) d m i =
      jetSubstPS (m := m) (fun p : Fin 1 × Fin d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin d) S)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X m _ (fun p => MvPowerSeries.constantCoeff_X _) p, ← MvPolynomial.coe_X, psJet_coe]
  unfold jetCopy
  rw [jetMap_mk, MvPolynomial.aeval_X]

theorem psJet_subst_trunc (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : MvPowerSeries κ S) :
    psJet m (MvPowerSeries.subst Q ((psTrunc m f : MvPolynomial κ S) : MvPowerSeries κ S)) =
      psJet m (MvPowerSeries.subst Q f) := by
  rw [psJet_subst m Q hQ, psJet_subst m Q hQ, psJet_coe]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinR
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts ComplexConjugate

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def bs (b : Basis ι ℤ Y) (a : ι) : Y →ₗ[ℤ] ℝ := Algebra.linearMap ℤ ℝ ∘ₗ b.coord a

theorem bs_apply (b : Basis ι ℤ Y) (a : ι) (y : Y) : bs b a y = (b.repr y a : ℝ) := by
  simp [bs]

theorem gram_expand (b : Basis ι ℤ Y) (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (v w : Y) :
    ∑ a, ∑ c, β (b a) (b c) * (bs b a v * bs b c w) = β v w := by
  conv_rhs => rw [← b.sum_repr v, ← b.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, bs_apply, zsmul_eq_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

section Repro

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

theorem repro_sigma (b : Basis ι ℤ Y) (β : SymB cj Y) (σ : E →+* ℂ) (y z : Y) :
    ∑ a, ∑ c, ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z)) =
      comp ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ).flip z) σ y := by
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB
  obtain ⟨_, hbal⟩ := β.2

  have hj : ∀ j, ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) * σ (ed E i)
      = star (σ (RingOfIntegers.basis E j : E)) * comp (B.flip z) σ y := by
    intro j
    obtain ⟨c, hc⟩ := cj_integral hcj (RingOfIntegers.basis E j)
    have hcc : ((RingOfIntegers.basis E j : 𝓞 E) : E) = cj (c : E) := by rw [hc, cj_cj hcj]
    have e : ∀ i, B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) =
        B (RingOfIntegers.basis E i • (c • y)) z := by
      intro i
      rw [← hbal c _ hcc, smul_comm]
    simp_rw [e]
    rw [show ∑ i, (B (RingOfIntegers.basis E i • (c • y)) z : ℂ) * σ (ed E i) = comp (B.flip z) σ (c • y)
      from rfl, comp_smul, hc, hcj]
  have e2 : ∀ c, conj (comp (bs b c) σ z) =
      ∑ j, (bs b c (RingOfIntegers.basis E j • z) : ℂ) * conj (σ (ed E j)) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [comp, map_sum]
  have expand : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z)) =
      ∑ j, conj (σ (ed E j)) * ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) *
        σ (ed E i) := by
    simp_rw [← gram_expand b B (RingOfIntegers.basis E _ • y) (RingOfIntegers.basis E _ • z)]
    simp_rw [e2]
    simp only [comp, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum,
      Complex.ofReal_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [expand]
  simp_rw [hj]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have ho := ortho σ σ
  simp only [if_true, integralBasis_apply] at ho
  have : ∑ j, conj (σ (ed E j)) * star (σ (RingOfIntegers.basis E j : E)) = 1 := by
    have := congrArg conj ho
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_mul] using this
  rw [this, one_mul]

theorem fock_reproducing_formula (b : Basis ι ℤ Y) (β : SymB cj Y) (y z : Y) :
    ∑ a, ∑ c, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) * Pf E (bs b a) (bs b c) y z =
      2 * (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z := by
  obtain ⟨hs, _⟩ := β.2
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB
  have key : ∀ σ : E →+* ℂ, ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z) + comp (bs b c) σ y * conj (comp (bs b a) σ z)) =
      2 * comp (B.flip z) σ y := by
    intro σ
    simp only [mul_add, Finset.sum_add_distrib]
    have sw : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b c) σ y * conj (comp (bs b a) σ z)) =
        ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
      rw [hs (b w) (b x)]
    rw [sw, repro_sigma hcj b β σ y z]
    ring
  unfold Pf
  have e : ∀ a c, B (b a) (b c) *
      (∑ σ : E →+* ℂ, (comp (bs b a) σ y * conj (comp (bs b c) σ z) +
        comp (bs b c) σ y * conj (comp (bs b a) σ z))).re =
      (∑ σ : E →+* ℂ, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z) +
        comp (bs b c) σ y * conj (comp (bs b a) σ z))).re := by
    intro a c
    rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  simp_rw [e]
  simp_rw [← Complex.re_sum]
  conv_lhs => arg 1; arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [key]
  rw [← Finset.mul_sum, sum_comp]
  simp [LinearMap.flip_apply]

theorem l_expand (b : Basis ι ℤ Y) (l : SymB cj Y →ₗ[ℝ] ℝ) (β : SymB cj Y) :
    l β = ∑ a, ∑ c, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) * (l (Pm hcj (bs b a) (bs b c)) / 2) := by
  have hsum : β = ∑ a, ∑ c, ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) / 2) • Pm hcj (bs b a) (bs b c) := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro y z
    have hP : ∀ (η ζ : Y →ₗ[ℤ] ℝ), ((Pm hcj η ζ : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z = Pf E η ζ y z :=
      fun _ _ => rfl
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, hP,
      smul_eq_mul]
    have := fock_reproducing_formula hcj b β y z
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, this]
    ring
  conv_lhs => rw [hsum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end Repro

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSpan
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

section

variable {E : Type} [Field E] [NumberField E] {cj : E → E} {Y : Type} [AddCommGroup Y]
  [Module (𝓞 E) Y]

theorem two_mul_form_half_unit (hcj : ∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) (w₀ : 𝓞 E)
    (hw : (w₀ : E) + cj w₀ = 1) (γ : SymB cj Y) (a : Y) :
    2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • a) a = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a := by
  obtain ⟨w', hw'⟩ := hcj w₀
  have mem : (∀ a d : Y, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) d a) ∧
      ∀ (c c' : 𝓞 E), (c' : E) = cj c → ∀ (a d : Y),
        (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • a) d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a (c' • d) := γ.2
  have h1 : w₀ + w' = 1 := by
    apply RingOfIntegers.ext
    first
      | (push_cast; rw [hw', hw])
      | simp [hw', hw]
  have h2 : (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • a) a = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w' • a) a := by
    rw [mem.2 w₀ w' hw' a a, mem.1]
  have h3 : (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) ((w₀ + w') • a) a = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a := by
    rw [h1, one_smul]
  rw [add_smul, map_add (f := _), LinearMap.add_apply, ← h2] at h3
  linarith

end

theorem bil_rad {Y : Type} [AddCommGroup Y] (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)
    (hsym : ∀ a b, γ a b = γ b a) (hpsd : ∀ a, 0 ≤ γ a a) (a : Y) (ha : γ a a = 0) (y : Y) :
    γ a y = 0 := by
  have key : ∀ n : ℤ, 0 ≤ (n : ℝ) * γ a y + (n : ℝ) * γ a y + γ y y := by
    intro n
    have h := hpsd (n • a + y)
    simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, zsmul_eq_mul, ha,
      hsym y a, mul_zero, zero_add] at h
    linarith
  by_contra hs
  obtain ⟨N, hN⟩ := exists_nat_gt (γ y y / (2 * |γ a y|))
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have h := key N
    rw [abs_of_neg hneg, div_lt_iff₀ (by linarith)] at hN
    push_cast at h
    nlinarith
  · have h := key (-(N : ℤ))
    rw [abs_of_pos hpos, div_lt_iff₀ (by linarith)] at hN
    push_cast at h
    nlinarith

theorem phiCSpan_holds : PhiCSpanStatement := by
  intro E _ _ cj hcj Y _ _ w₀ hw β hβ k x hx
  unfold phiC
  let l : SymB cj Y →ₗ[ℝ] ℝ :=
    { toFun := fun γ => ∑ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i)
      map_add' := fun γ γ' => by simp [Finset.sum_add_distrib]
      map_smul' := fun r γ => by simp [Finset.mul_sum] }
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨l', -, hpos, he⟩
    by_cases h0 : β = 0
    · rw [he, h0, map_zero]
    · rw [he]
      exact (hpos β hβ h0).le
  · refine ⟨l, ?_, ?_, rfl⟩
    · intro γ hγ
      choose z hz using fun i => hγ (w₀ • x i) (x i)
      refine ⟨∑ i, z i, ?_⟩
      show ∑ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i) = ((∑ i, z i : ℤ) : ℝ)
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun i _ => hz i
    · intro γ hγ hne
      have mem : (∀ a d : Y, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) d a) ∧
          ∀ (c c' : 𝓞 E), (c' : E) = cj c → ∀ (a d : Y),
            (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • a) d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a (c' • d) := γ.2
      have hsum : ∀ i, 2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i) =
          (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x i) := fun i => two_mul_form_half_unit hcj w₀ hw γ (x i)
      have hnn : ∀ i, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i) := fun i => by
        have := hγ (x i)
        linarith [hsum i]
      show 0 < ∑ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i)
      rcases (Finset.sum_nonneg fun i _ => hnn i).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        apply hne
        have hz : ∀ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x i) = 0 := by
          intro i
          have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp heq.symm i
            (Finset.mem_univ i)
          linarith [hsum i]
        have hrad : ∀ i y, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) y = 0 :=
          fun i y => bil_rad _ mem.1 hγ (x i) (hz i) y
        have hspan : ∀ u ∈ Submodule.span (𝓞 E) (Set.range x), ∀ y,
            (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) u y = 0 := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem u hu =>
            obtain ⟨i, rfl⟩ := hu
            exact hrad i
          | zero => intro y; simp
          | add u v _ _ hu hv => intro y; simp [hu y, hv y]
          | smul c u _ hu =>
            intro y
            obtain ⟨c', hc'⟩ := hcj c
            rw [mem.2 c c' hc' u y]
            exact hu _
        apply Subtype.ext
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro z
        obtain ⟨n, hn, hny⟩ := hx y
        have h1 := hspan _ hny z
        simp only [map_nsmul, map_zsmul, LinearMap.smul_apply, nsmul_eq_mul, zsmul_eq_mul] at h1
        rw [show ((0 : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) = 0 from rfl, LinearMap.zero_apply,
          LinearMap.zero_apply]
        rcases mul_eq_zero.mp h1 with h | h
        · first
            | exact absurd h (Nat.cast_ne_zero.mpr hn.ne')
            | exact absurd h (Int.cast_ne_zero.mpr hn.ne')
        · exact h

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

