module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DeRhamInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDefs
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

section An

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

def Sz (k : ℕ) (f : V → F) (p : V) (b : ℝ) : Prop := ∀ i ≤ k, ‖iteratedFDeriv ℝ i f p‖ ≤ b

theorem Sz.mono {k : ℕ} {f : V → F} {p : V} {b c : ℝ} (h : Sz k f p b) (hb : b ≤ c) : Sz k f p c :=
  fun i hi => (h i hi).trans hb

theorem Sz.of_le {k l : ℕ} {f : V → F} {p : V} {b : ℝ} (h : Sz k f p b) (hl : l ≤ k) : Sz l f p b :=
  fun i hi => h i (hi.trans hl)

theorem Sz.norm_le {k : ℕ} {f : V → F} {p : V} {b : ℝ} (h : Sz k f p b) : ‖f p‖ ≤ b := by
  simpa using h 0 (Nat.zero_le k)

theorem Sz.nonneg {k : ℕ} {f : V → F} {p : V} {b : ℝ} (h : Sz k f p b) : 0 ≤ b := (norm_nonneg _).trans h.norm_le

theorem Sz.congr {k : ℕ} {f g : V → F} {p : V} {b : ℝ} (h : Sz k f p b) (e : f =ᶠ[𝓝 p] g) : Sz k g p b :=
  fun i hi => by rw [← (e.iteratedFDeriv ℝ i).eq_of_nhds]; exact h i hi

theorem exists_sz (k : ℕ) (f : V → F) (p : V) : ∃ b, Sz k f p b :=
  ⟨∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i f p‖, fun i hi =>
    Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f p‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))⟩

def tp (A : V →L[ℝ] V) (B : F →L[ℝ] F) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  B.compContinuousAlternatingMap ((w (A p)).compContinuousLinearMap A)

theorem tp_apply (A : V →L[ℝ] V) (B : F →L[ℝ] F) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (v : Fin q → V) :
    tp A B w p v = B (w (A p) fun i => A (v i)) := rfl

end An

section Geo

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

def Inv {q : ℕ} (w : G.Om q) : Prop := ∀ γ, G.act q γ w = w

def IsFun (Φ : S → V → ℝ) : Prop :=
  (∀ s, ContDiffOn ℝ ∞ (Φ s) G.Y) ∧ (∀ γ s, ∀ p ∈ G.Y, Φ (G.σ γ s) (G.ρ γ p) = Φ s p) ∧
    ∀ s (t : ℝ), 0 < t → ∀ p ∈ G.Y, Φ s (t • p) = Φ s p

end Geo

section Ad

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def pt (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : GA E a := infGL E a g * finGL E a x

theorem pt_mul (g h : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : pt (g * h) x = pt g x * infGL E a h := by
  rw [pt, pt, map_mul, mul_assoc, infGL_comm, mul_assoc]


omit [_root_.NumberField.IsTotallyComplex E] in
def Bnd (c : ℝ) (h : GL (Fin a) (Cinf E)) : Prop := ‖toL h.val‖ ≤ c ∧ ‖toL (h⁻¹).val‖ ≤ c

structure IsLam (lam : GA E a → ℝ) : Prop where
  add : ∀ g h, lam (g * h) = lam g + lam h
  split : ∀ g, splitCentre E a (lam g) * (retractOne g : KernelIndexFullLattice.G1 E a).1 = g
  bdd : ∀ c : ℝ, ∃ B : ℝ, ∀ h, Bnd c h → |lam (infGL E a h)| ≤ B

variable (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)

abbrev Fm (q : ℕ) : Type := (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)

def Tw {q : ℕ} (w : Fm U Ξ q) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ) :=
  tp (sand g) (mulVecL (Ξ.mat g⁻¹)) (w (x : GL (Fin a) (Af E) ⧸ U))

def Dec (f lam : GA E a → ℝ) (f₀ : ℝ) (k : ℕ) (A B M : ℝ) {q : ℕ} (w : Fm U Ξ q) : Prop :=
  ∀ g x, f₀ ≤ f (pt g x) → Sz k (Tw U Ξ w g x) (hOne E a) (M * Real.exp (B * |lam (pt g x)| - A * f (pt g x)))

theorem Dec.mono {f lam : GA E a → ℝ} {f₀ f₁ : ℝ} {k : ℕ} {A B M : ℝ} {q : ℕ} {w : Fm U Ξ q}
    (h : Dec U Ξ f lam f₀ k A B M w) (hf : f₀ ≤ f₁) : Dec U Ξ f lam f₁ k A B M w := fun g x hg => h g x (hf.trans hg)

theorem Dec.of_le {f lam : GA E a → ℝ} {f₀ : ℝ} {k : ℕ} {A B M M' : ℝ} {q : ℕ} {w : Fm U Ξ q}
    (h : Dec U Ξ f lam f₀ k A B M w) (hM : M ≤ M') : Dec U Ξ f lam f₀ k A B M' w :=
  fun g x hg => (h g x hg).mono (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le)

theorem Tw_one {q : ℕ} (w : Fm U Ξ q) (x : GL (Fin a) (Af E)) : Tw U Ξ w 1 x = w (x : GL (Fin a) (Af E) ⧸ U) := by
  funext p
  ext v j
  simp [Tw, tp_apply]

theorem Tw_eq {q : ℕ} (w : Fm U Ξ q) (g h : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    Tw U Ξ w g x = tp (sand h⁻¹) (mulVecL (Ξ.mat h)) (Tw U Ξ w (g * h) x) := by
  have e : ∀ p : HV E a, sand (g * h) (sand h⁻¹ p) = sand g p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
  funext p
  refine ContinuousAlternatingMap.ext fun v => ?_
  simp only [Tw, tp_apply, e, mulVecL_apply, Matrix.mulVec_mulVec, ← map_mul, _root_.mul_inv_rev, mul_inv_cancel_left]

def Desc (f : GA E a → ℝ) (Φ : (GL (Fin a) (Af E) ⧸ U) → HV E a → ℝ) : Prop :=
  ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)), Φ (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a)) = f (pt g x)


omit [_root_.NumberField.IsTotallyComplex E] in
def Zw (Z : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (p : HV E a) :
    HV E a := sand g⁻¹ (Z (x : GL (Fin a) (Af E) ⧸ U) (sand g p))

end Ad

end UpperTheory.V.Lit.Geo.Cs
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
section
noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo

def OneStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ η : Co Ξ q, IsLev U Ξ η →
      ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧ ∀ (g : GA E a) (M M' : ℝ), 0 ≤ M → 0 ≤ M' →
        (∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + (Y g).1 → Bd η (g * infGL E a h) M) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 →
          Bd (Ξ := Ξ) (dCo (smLie Ξ) η) (g * infGL E a h) M') → Bd η' g (B * (M + M'))

def BdBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ),
    ∃ (T : Finset (Fin q → Herm E a)) (B : ℝ), 0 ≤ B ∧ ∀ (α : Co Ξ q) (g : GA E a) (M : ℝ), 0 ≤ M →
      (∀ X ∈ T, ‖ev (α X) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ M) → Bd α g (B * M)

def BdCompact : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ R : ℝ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ g : GA E a, qht g ≤ R → Bd α g M

def BdGrowth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q),
    (Moderate α → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ g : GA E a, Bd α g (C * qht g ^ N)) ∧
    (Rapid α → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E a, Bd α g (C / qht g ^ N))

def Prim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ),
    IsStep U f Y C c f₀ → ∀ (q : ℕ) (η : Co Ξ q), IsLev U Ξ η → Moderate (Ξ := Ξ) (dCo (smLie Ξ) η) →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧
        ∀ g : GA E a, f g ≤ n * c → Bd η' g (Real.exp (D * (n + 1)))

def CutBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (u : Sm E a) (η ζ : Co Ξ q),
    (∀ (X : Fin (q + 1) → Herm E a) g, ev (dCo (smLie Ξ) ζ X) g = u.1 g • ev (dCo (smLie Ξ) η X) g +
      ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * (lie E a (toL (X i).1) u).1 g) • ev (η (i.removeNth X)) g) →
    ∀ (g : GA E a) (s b M M' : ℝ), 0 ≤ M → 0 ≤ M' → 0 ≤ b →
      ‖1 - u.1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ s →
      (∀ X, ‖(lie E a X u).1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ b * ‖X‖) →
      (b = 0 ∨ Bd η g M) → Bd (Ξ := Ξ) (dCo (smLie Ξ) η) g M' →
      Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g (s * M' + (q + 1) * b * M)

def Approx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ U : Subgroup (GL (Fin a) (Af E)),
    IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (η : Co Ξ q),
    IsLev U Ξ η → Moderate (Ξ := Ξ) (dCo (smLie Ξ) η) → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ R : ℝ, ∃ ζ : Co Ξ q, IsLev U Ξ ζ ∧
      CSupp ζ ∧ CSupp (Ξ := Ξ) (dCo (smLie Ξ) ζ) ∧ ∀ g : GA E a,
        (qht g ≤ R → Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g 0) ∧
        Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g (C * qht g ^ N)

def PtRetr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a),
    IsData Ξ r χ G e → ∀ (q : ℕ) (α β : Co Ξ q), IsLev U Ξ α → IsLev U Ξ β → ∀ g : GA E a,
      ptIp χ G e α β g = ∑ I : Fin q → Fin n,
        star (ev (α fun i => e (I i)) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1) ⬝ᵥ
          G *ᵥ ev (β fun i => e (I i)) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1

def PtBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a),
    IsData Ξ r χ G e → ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → ∀ (g : GA E a) (M M' : ℝ),
      0 ≤ M → 0 ≤ M' → Bd α g M → Bd β g M' → ‖ptIp χ G e α β g‖ ≤ B * M * M'

theorem ptIp_sub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ} (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a) (α β β' : Co Ξ q) (g : GA E a) :
    ptIp χ G e α (β - β') g = ptIp χ G e α β g - ptIp χ G e α β' g := by
  simp only [ptIp, AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, dotProduct_sub,
    Finset.sum_sub_distrib, mul_sub]

theorem firstGeometricCondition_of_properties (h1 : PairFacts) (h2 : QhtFacts) (h3 : LevD) (h4 : BdGrowth) (h5 : Approx) (h6 : PtBd)
    (h7 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure],
      IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)) : G1 := by
  intro E _ _ _ a ha μ _ U hUo hUc Ξ r χ G n e hD q β η hβ hη hR hδ hM
  haveI := h7 E a μ
  obtain ⟨N, C, hC, hA⟩ := h5 E a ha U hUo hUc Ξ q η hη hM
  obtain ⟨C', hC', hB⟩ := (h4 E a Ξ (q + 1) β).2 hR (N + 1)
  obtain ⟨B, hB0, hP⟩ := h6 E a ha U hUo Ξ r χ G n e hD (q + 1)
  have hdη := (h3 E a U Ξ q η hη).1
  have hq := (h2 E a).1
  have key : ∀ R : ℝ, 0 < R → ‖pair μ χ G e β (dCo (smLie Ξ) η)‖ ≤
      B * C' * C * (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ).real Set.univ / R := fun R hR0 => by
    obtain ⟨ζ, hζ, hc, hc', hg⟩ := hA R
    have hdζ := (h3 E a U Ξ q ζ hζ).1
    have hγ := (h3 E a U Ξ (q + 1) _ hdη).2 _ hdζ
    have i1 := (h1 E a ha μ U hUo Ξ r χ G n e hD (q + 1)).1 β _ hβ hdη hR hM
    have i2 := ((h1 E a ha μ U hUo Ξ r χ G n e hD (q + 1)).2.1 _ β hdζ hβ hc').2
    have z : pair μ χ G e β (dCo (smLie Ξ) ζ) = 0 := by
      rw [(h1 E a ha μ U hUo Ξ r χ G n e hD q).2.2.2 β ζ hβ hζ (Or.inr hc), hδ]
      simp [pair, ptIp]
    have e1 : pair μ χ G e β (dCo (smLie Ξ) η) = pair μ χ G e β (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) := by
      rw [← sub_zero (pair μ χ G e β (dCo (smLie Ξ) η)), ← z]
      simp only [pair, ptIp_sub]
      exact (integral_sub i1 i2).symm
    rw [e1, mul_div_right_comm]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
    have q1 := hq x.out
    have q0 : 0 < qht x.out := one_pos.trans_le q1
    by_cases hx : qht x.out ≤ R
    · refine (hP β _ hβ hγ x.out _ 0 (by positivity) le_rfl (hB _) ((hg _).1 hx)).trans ?_
      rw [mul_zero]
      positivity
    · refine (hP β _ hβ hγ x.out _ _ (by positivity) (by positivity) (hB _) (hg _).2).trans ?_
      have e2 : B * (C' / qht x.out ^ (N + 1)) * (C * qht x.out ^ N) = B * C' * C / qht x.out := by
        field_simp
        ring
      rw [e2]
      exact div_le_div_of_nonneg_left (by positivity) hR0 (not_le.1 hx).le
  exact norm_le_zero_iff.1 (ge_of_tendsto (tendsto_const_nhds.div_atTop Filter.tendsto_id)
    ((Filter.eventually_gt_atTop 0).mono key))

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerKer
section
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Geo

section

variable {Γ M N : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

omit [Group Γ] [Module ℂ M] in
private theorem hd_cons (c : List Γ → M) (g : Γ) (x : List Γ) : hd c (g :: x) = c x - hd (fun y => c (g :: y)) x := by
  simp only [hd, List.length_cons, Finset.sum_range_succ', List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, pow_succ,
    mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, pow_zero, one_smul]
  abel

omit [Group Γ] [Module ℂ M] in
private theorem hd_congr {c c' : List Γ → M} {k : ℕ} (h : ∀ x : List Γ, x.length = k → c x = c' x) (x : List Γ)
    (hx : x.length = k + 1) : hd c x = hd c' x :=
  Finset.sum_congr rfl fun i hi => by
    rw [h _ (by rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi), hx]; rfl)]

omit [Group Γ] [Module ℂ M] in
private theorem hd_sub (c c' : List Γ → M) (x : List Γ) : hd (fun y => c y - c' y) x = hd c x - hd c' x := by
  simp only [hd, smul_sub, Finset.sum_sub_distrib]

omit [Group Γ] in
private theorem hd_map (f : M →ₗ[ℂ] N) (c : List Γ → M) (x : List Γ) : hd (fun y => f (c y)) x = f (hd c x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hd, map_sum, map_zsmul]

omit [Group Γ] [Module ℂ M] in
private theorem hd_hd (x : List Γ) : ∀ c : List Γ → M, hd (hd c) x = 0 := by
  induction x with
  | nil => intro c; simp [hd]
  | cons g x ih =>
    intro c
    rw [hd_cons]
    simp only [hd_cons]
    rw [hd_sub, ih]
    simp

private theorem hequiv_sub {ρ : Representation ℂ Γ M} {k : ℕ} {c c' : List Γ → M} (h : HEquiv ρ k c) (h' : HEquiv ρ k c') :
    HEquiv ρ k fun y => c y - c' y := fun γ x hx => by
  simp only [h γ x hx, h' γ x hx, map_sub]

private theorem contract {ρ : Representation ℂ Γ M} (hav : HasAverage ρ) {k : ℕ} {z : List Γ → M} (h : HEquiv ρ (k + 1) z)
    (hz : ∀ x : List Γ, x.length = k + 3 → hd z x = 0) :
    ∃ f, HEquiv ρ k f ∧ ∀ x : List Γ, x.length = k + 2 → z x = hd f x := by
  obtain ⟨P, h1, h2⟩ := hav
  refine ⟨fun x => P fun g => z (g :: x), fun γ x hx => ?_, fun x hx => ?_⟩
  · rw [h2]
    refine congrArg P (funext fun g => ?_)
    rw [← h γ _ (by simp [hx])]
    simp
  · rw [hd_map P (fun x g => z (g :: x)), ← h1 (z x)]
    congr 1
    funext g
    have := hz (g :: x) (by simp [hx])
    rw [hd_cons, sub_eq_zero] at this
    rw [this]
    simp [hd]

private theorem lift_ex {ρ : Representation ℂ Γ M} {σ : Representation ℂ Γ N} (f : M →ₗ[ℂ] N)
    (hf : ∀ γ m, f (ρ γ m) = σ γ (f m)) {k : ℕ} {e : List Γ → N} (h : HEquiv σ k e)
    (he : ∀ x : List Γ, x.length = k + 1 → ∃ m, f m = e x) :
    ∃ b, HEquiv ρ k b ∧ ∀ x : List Γ, x.length = k + 1 → f (b x) = e x := by
  classical
  choose! s hs using he
  refine ⟨fun x => ρ (x.headD 1) (s (x.map ((x.headD 1)⁻¹ * ·))), fun γ x hx => ?_, fun x hx => ?_⟩
  · cases x with
    | nil => simp at hx
    | cons g x =>
      have : ∀ y : Γ, (γ * g)⁻¹ * (γ * y) = g⁻¹ * y := fun y => by group
      simp only [List.map_cons, List.headD_cons, List.map_map, Function.comp_def, this, map_mul, Module.End.mul_apply]
  · rw [hf, hs _ (by simp [hx]), ← h _ _ (by simp [hx])]
    simp [Function.comp_def]

private theorem hequiv_hd {ρ : Representation ℂ Γ M} {k : ℕ} {c : List Γ → M} (h : HEquiv ρ k c) :
    HEquiv ρ (k + 1) (hd c) := fun γ x hx => by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hd, map_sum, map_zsmul, List.length_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [List.eraseIdx_map, h γ _ (by rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi), hx]; rfl)]

end

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
  (G : Dr.Geo Γ V S d)

private theorem zig_pos (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (hav : ∀ q, HasAverage (G.act q))
    (c : List Γ → S → Fin d → ℂ) (n q : ℕ) : ∀ (k : ℕ) (u : List Γ → G.Om q), n = q + k → Zig G q (k + 1) u c →
    (HCob G.lev (n + 1) c ↔ ∃ e : List Γ → G.Om q, HEquiv (G.act q) k e ∧
      (∀ x : List Γ, x.length = k + 1 → G.dOm q (e x) = 0) ∧ ∀ x : List Γ, x.length = k + 2 → u x = hd e x) := by
  obtain ⟨a1, a2, a3⟩ := inclFacts Γ V S d G hc hn
  induction q with
  | zero =>
    intro k u hk hz
    obtain rfl : n = k := by omega
    constructor
    · rintro ⟨b, hb, hb'⟩
      refine ⟨fun x => G.incl (b x), fun γ x hx => ?_, fun x _ => a3.apply_apply_eq_zero _, fun x hx => ?_⟩
      · simp only [hb γ x hx, a1]
      · rw [hd_map, hz x hx, hb' x hx]
    · rintro ⟨e, h1, h2, h3⟩
      obtain ⟨b, hb, hb'⟩ := lift_ex G.incl a1 h1 fun x hx => (a3 _).1 (h2 x hx)
      refine ⟨b, hb, fun x hx => a2 ?_⟩
      rw [← hz x hx, h3 x hx, ← hd_map, hd_congr hb' x hx]
  | succ q ih =>
    rintro k u hk ⟨b, hb, hb', hz⟩
    rw [ih (k + 1) (hd b) (by omega) hz]
    constructor
    · rintro ⟨e, h1, h2, h3⟩
      obtain ⟨f, hf, hf'⟩ := contract (hav q) (hequiv_sub hb h1) fun x hx => by rw [hd_sub, h3 x hx, sub_self]
      refine ⟨fun x => G.dOm q (f x), fun γ x hx => ?_, fun x _ => (dExact Γ V S d G hc q).apply_apply_eq_zero _,
        fun x hx => ?_⟩
      · simp only [hf γ x hx, dEquiv Γ V S d G]
      · rw [hd_map, ← hf' x hx, map_sub, h2 x hx, hb' x hx, sub_zero]
    · rintro ⟨e, h1, h2, h3⟩
      obtain ⟨f, hf, hf'⟩ := lift_ex (G.dOm q) (dEquiv Γ V S d G q) h1 fun x hx =>
        (dExact Γ V S d G hc q _).1 (h2 x hx)
      refine ⟨fun x => b x - hd f x, hequiv_sub hb (hequiv_hd hf), fun x hx => ?_, fun x _ => ?_⟩
      · rw [map_sub, hb' x hx, h3 x hx, ← hd_map, hd_congr hf' x hx, sub_self]
      · rw [hd_sub, hd_hd, sub_zero]

private theorem zig_top (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (hav : ∀ q, HasAverage (G.act q))
    (c : List Γ → S → Fin d → ℂ) (q : ℕ) (w : G.Om q) (hz : Zig G q 0 (fun _ => w) c) :
    HCob G.lev q c ↔ InvExact (Ω := fun q => G.Om q) G.act G.dOm w := by
  obtain ⟨a1, a2, a3⟩ := inclFacts Γ V S d G hc hn
  have h2 : ∀ {M : Type} [AddCommGroup M] (e : List Γ → M) (g h : Γ), hd e [g, h] = e [h] - e [g] := fun e g h => by
    simp [hd, Finset.sum_range_succ, sub_eq_add_neg]
  cases q with
  | zero =>
    constructor
    · intro h
      have := hz [1] rfl
      rw [h [1] rfl, map_zero] at this
      exact this
    · intro h x hx
      have h0 : w = 0 := h
      exact a2 (by rw [← hz x hx, map_zero]; exact h0)
  | succ q =>
    obtain ⟨b, hb, hb', hz⟩ := hz
    rw [zig_pos G hc hn hav c q q 0 (hd b) rfl hz]
    constructor
    · rintro ⟨e, e1, e2, e3⟩
      refine ⟨b [1] - e [1], fun γ => ?_, ?_⟩
      · have := e3 [1, γ] rfl
        rw [h2, h2] at this
        have h4 := hequiv_sub hb e1 γ [1] rfl
        simp only [List.map_cons, List.map_nil, mul_one] at h4
        rw [← h4]
        exact sub_eq_sub_iff_sub_eq_sub.1 this
      · rw [map_sub, e2 [1] rfl, hb' [1] rfl, sub_zero]
    · rintro ⟨y, y1, y2⟩
      refine ⟨fun x => b x - y, hequiv_sub hb fun γ x _ => (y1 γ).symm, fun x hx => ?_, fun x hx => ?_⟩
      · rw [map_sub, hb' x hx, y2, sub_self]
      · obtain ⟨g, h, rfl⟩ := List.length_eq_two.1 hx
        rw [h2, h2]
        abel

end

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.perKer :
    PerKer := by
  rintro E _ _ _ a ha U hU Ξ q α c hα ⟨ho, w, hw, hz⟩
  obtain ⟨W, hW⟩ := window _ _ _ _ (geo ho U Ξ) (geoProper E a ho U Ξ hU)
  obtain ⟨u, hu⟩ := cutoff _ _ _ _ (geo ho U Ξ) W hW
  rw [← geo_lev ho U Ξ, zig_top (geo ho U Ξ) (coneConvex E a).1 ⟨_, hOne_mem_cone⟩ (average _ _ _ _ _ u hu) c q w hz]
  cases q with
  | zero =>
    constructor
    · intro h
      obtain rfl : w = 0 := h
      exact (corrUniq E a ho U Ξ 0).1 _ 0 _ hw (corr_zero U Ξ)
    · intro h
      obtain rfl : α = 0 := h
      exact (corrUniq E a ho U Ξ 0).2 0 _ 0 hw (corr_zero U Ξ)
  | succ q =>
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨l, hl⟩ := gauge E a ha ho U Ξ hU
      obtain ⟨y', i1, i2, i3⟩ := retract _ _ _ _ (geo ho U Ξ) (coneConvex E a).2 l hl q y hy
        ((corrBasic E a U Ξ _ _ _ hw).1 hα.basic)
      obtain ⟨η, hη⟩ := corrBwd E a ho U Ξ q y'
      have e : dCo (smLie Ξ) η = α := (corrUniq E a ho U Ξ (q + 1)).1 _ _ _ (i3 ▸ corrD E a ho U Ξ q _ _ hη) hw
      have b := (corrBasic E a U Ξ _ _ _ hη).2 i2
      obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hη
      exact ⟨η, ⟨c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hη).2 i1 X) (c2 X)
        (centralOf E a _ (smLie Ξ) q η b (e ▸ hα.basic) X)⟩, e⟩
    · rintro ⟨η, hη, rfl⟩
      have hv : ∀ X, LeftInv (η X) ∧ RightInv U (η X) := fun X => (levelVal E a U Ξ _).1 (hη.val X)
      obtain ⟨y, hy, h0⟩ := corrFwd E a U Ξ q η hη.equiv fun X => (hv X).2
      let y' : (geo ho U Ξ).Om q := ⟨y, fun s => ⟨corrSmooth E a U Ξ q _ y hy s, h0 s⟩⟩
      exact ⟨y', (corrInv E a ho U Ξ q _ y' hy).1 fun X => (hv X).1,
        (corrUniq E a ho U Ξ (q + 1)).2 _ _ _ (corrD E a ho U Ξ q _ y' hy) hw⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfRapidBdd
section
open UpperTheory.V.Lit.Geo
open Matrix

private theorem norm_form_le {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d → ℂ) :
    ‖star x ⬝ᵥ G *ᵥ y‖ ≤ (∑ i, ∑ j, ‖G i j‖) * (‖x‖ * ‖y‖) := by
  simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, Pi.star_apply, norm_star, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm y j) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

private theorem mul_le_of_bounds {u v t A B : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (h1 : u * t ≤ A) (h2 : v ≤ B * t) :
    u * v ≤ |B| * A :=
  calc u * v ≤ u * (|B| * t) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right (le_abs_self B) ht)) hu
    _ = |B| * (u * t) := by ring
    _ ≤ |B| * A := mul_le_mul_of_nonneg_left h1 (abs_nonneg B)

theorem UpperTheory.V.Lit.Geo.Pf.rapidBdd :
    UpperTheory.V.Lit.Geo.Pf.RapidBdd := by
  intro E _ _ _ a Ξ χ s hs G n e q α β hα hβ
  obtain ⟨N, hN⟩ := hβ
  choose B hB using hN
  choose A hA using fun X => hα X N
  refine ⟨∑ I : Fin q → Fin n, (∑ i, ∑ j, ‖G i j‖) * (|B fun i => e (I i)| * A fun i => e (I i)), fun g => ?_⟩
  have h1 := Pf.chiOne E a χ s hs g
  have hq : 0 ≤ qht (E := E) (a := a) g.1 ^ N := pow_nonneg (zero_le_one.trans ((qhtFacts E a).1 _)) N
  unfold ptIp
  rw [h1, one_pow, Complex.ofReal_one, one_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => (norm_form_le G _ _).trans ?_)
  exact mul_le_mul_of_nonneg_left (mul_le_of_bounds (norm_nonneg _) hq (hA _ g) (hB _ g))
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
end

