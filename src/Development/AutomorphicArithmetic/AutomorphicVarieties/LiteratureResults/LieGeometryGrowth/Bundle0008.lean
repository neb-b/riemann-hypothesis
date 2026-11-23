module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BdBasis
section
open UpperTheory.V.Lit.Geo

private theorem absBd {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : W ≃ₗ[ℝ] V) (q : ℕ) :
    ∃ (T : Finset (Fin q → W)) (B : ℝ), 0 ≤ B ∧ ∀ (m : (Fin q → W) →ₘₗ[ℝ] F) (M : ℝ), 0 ≤ M →
      (∀ X ∈ T, ‖m X‖ ≤ M) → ∀ X, ‖m X‖ ≤ B * M * ∏ i, ‖e (X i)‖ := by
  classical
  let b := Module.finBasis ℝ V
  let c : Fin (Module.finrank ℝ V) → (V →L[ℝ] ℝ) := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  refine ⟨Finset.univ.image fun I : Fin q → Fin (Module.finrank ℝ V) => fun i => e.symm (b (I i)),
    ∑ I : Fin q → Fin (Module.finrank ℝ V), ∏ i, ‖c (I i)‖, by positivity, fun m M hM hT X => ?_⟩
  have hX : X = fun i => ∑ j, c j (e (X i)) • e.symm (b j) := by
    funext i
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    exact (b.sum_repr _).symm
  have h1 : m X = ∑ I : Fin q → Fin (Module.finrank ℝ V),
      (∏ i, c (I i) (e (X i))) • m fun i => e.symm (b (I i)) := by
    conv_lhs => rw [hX]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [m.map_sum]
    exact Finset.sum_congr rfl fun I _ => m.map_smul_univ _ _
  rw [h1, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  rw [norm_smul, norm_prod, mul_right_comm, ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => (c (I i)).le_opNorm _)
    (hT _ (Finset.mem_image_of_mem _ (Finset.mem_univ I))) (norm_nonneg _) (by positivity)

theorem UpperTheory.V.Lit.Geo.bdBasis :
    BdBasis := by
  intro E _ _ _ a Ξ q
  obtain ⟨T, B, hB, h⟩ := absBd (F := Fin Ξ.d → ℂ) (UpperTheory.V.Lit.Dr.hv (E := E) (a := a)) q
  refine ⟨T, B, hB, fun α g M hM hT X => ?_⟩
  exact h ((((LinearMap.proj _).comp UpperTheory.V.Lit.Dr.ev).restrictScalars ℝ).compMultilinearMap α.toMultilinearMap) M hM hT X
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

def CompSz : Prop :=
  ∀ (V W F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : W → F) (f : V → W) (x : V) (b : ℝ),
    ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g (f x) → (∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ c) →
    Sz k g (f x) b → Sz k (fun y => g (f y)) x (C * b)

def AppSz : Prop :=
  ∀ (V W F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (x : V),
    (∀ (f : V → W →L[ℝ] F) (g : V → W) (a b : ℝ), ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g x → Sz k f x a → Sz k g x b →
      Sz k (fun y => f y (g y)) x (2 ^ k * a * b)) ∧
    (∀ (L : W →L[ℝ] F) (g : V → W) (b : ℝ), ContDiffAt ℝ ∞ g x → Sz k g x b → Sz k (fun y => L (g y)) x (‖L‖ * b)) ∧
    ∀ (ι : Type) (s : Finset ι) (g : ι → V → F) (b : ι → ℝ), (∀ i ∈ s, ContDiffAt ℝ ∞ (g i) x) → (∀ i ∈ s, Sz k (g i) x (b i)) →
      Sz k (fun y => ∑ i ∈ s, g i y) x (∑ i ∈ s, b i)

def AltSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ) (c : ℝ),
    ContDiff ℝ ∞ (fun L : V →L[ℝ] V => (ContinuousAlternatingMap.compContinuousLinearMapCLM L :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F))) ∧
    ∃ C : ℝ, ∀ L : V →L[ℝ] V, ‖L‖ ≤ c → Sz k (fun L : V →L[ℝ] V => (ContinuousAlternatingMap.compContinuousLinearMapCLM L :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F))) L C

def AltEv : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ),
    ∃ (T : Finset (Fin q → V)) (C : ℝ), 0 ≤ C ∧ ∀ (f : V → V [⋀^Fin q]→L[ℝ] F) (x : V) (b : ℝ), 0 ≤ b →
      (∀ v ∈ T, ContDiffAt ℝ ∞ (fun y => f y v) x) → (∀ v ∈ T, Sz k (fun y => f y v) x b) → Sz k f x (C * b)

def TpSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] (q k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : V →L[ℝ] V) (B : F →L[ℝ] F) (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (b : ℝ), ‖A‖ ≤ c → ‖B‖ ≤ c →
      ContDiffAt ℝ ∞ w (A p) → Sz k w (A p) b → Sz k (tp A B w) p (C * b)

def FlowSz : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) (c : ℝ) (W : V → V) (t : ℝ) (p : V), |t| ≤ 1 →
    ContDiffAt ℝ ∞ W p → Sz (k + 1) W p c → ContDiffAt ℝ ∞ (flow W t) p ∧ ContDiffAt ℝ ∞ (fderiv ℝ (flow W t)) p ∧
      Sz k (fderiv ℝ (flow W t)) p (1 + c) ∧ ∀ i, 1 ≤ i → i ≤ k + 1 → ‖iteratedFDeriv ℝ i (flow W t) p‖ ≤ 1 + c

def PbSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (W : V → V) (t : ℝ) (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (b : ℝ), |t| ≤ 1 → ContDiffAt ℝ ∞ W p → Sz (k + 1) W p c →
      ContDiffAt ℝ ∞ w (flow W t p) → Sz k w (flow W t p) b → Sz k (pb (flow W t) w) p (C * b)

def HkSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (W : V → V) (t : ℝ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (b : ℝ), |t| ≤ 1 → ContDiffAt ℝ ∞ W p →
      Sz (k + 1) W p c → ContDiffAt ℝ ∞ w (flow W t p) → Sz k w (flow W t p) b → Sz k (hk W t w) p (C * b)

def IntSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [CompleteSpace F] (k : ℕ) (p : V) (O : Set (V × ℝ))
    (Φ : V × ℝ → F) (b : ℝ), IsOpen O → (∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ O) → ContDiffOn ℝ ∞ Φ O →
    (∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k (fun x => Φ (x, t)) p b) → Sz k (fun x => ∫ t in (0 : ℝ)..1, Φ (x, t)) p b

def HomSz : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q k : ℕ) (c : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Y : Set V) (W : V → V) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (b : ℝ), IsOpen Y → IsField Y W → ContDiffOn ℝ ∞ w Y →
      ∀ p ∈ Y, Sz (k + 1) W p c → (∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k w (flow W t p) b) → Sz k (hom W w) p (C * b)

def SumSm : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Y : Set V), IsOpen Y → ∀ y : ℕ → V → F, (∀ j, ContDiffOn ℝ ∞ (y j) Y) →
    (∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j)) →
    ContDiffOn ℝ ∞ (fun x => ∑' j, y j x) Y ∧
      ∀ p ∈ Y, HasSum (fun j => fderiv ℝ (y j) p) (fderiv ℝ (fun x => ∑' j, y j x) p)

def GeoCut : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d)
    (Φ : S → V → ℝ), IsFun G Φ → ∀ (R : ℝ) (q : ℕ) (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)),
    (∀ s, ContDiffOn ℝ ∞ (η s) {p | p ∈ G.Y ∧ R < Φ s p}) →
    (∀ γ s, ∀ p ∈ G.Y, R < Φ s p → G.tr q γ (η (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) = η s p) →
    ∃ z : G.Om q, Inv G z ∧ ∀ s, ∀ p ∈ G.Y, R + 1 ≤ Φ s p → z.1 s p = η s p

def GeoSum : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d)
    (Φ : S → V → ℝ), IsFun G Φ → ∀ (R : ℝ) (q : ℕ) (y : ℕ → G.Om q) (w : ℕ → G.Om (q + 1)), (∀ j, Inv G (y j)) →
    (∀ j, G.dOm q (y j) = w (j + 1) - w j) →
    (∀ k s, ∀ p ∈ G.Y, R < Φ s p → ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k ((y j).1 s) x (b j)) →
    (∀ s, ∀ p ∈ G.Y, R < Φ s p → Filter.Tendsto (fun j => (w j).1 s p) Filter.atTop (𝓝 0)) →
    ∃ z : G.Om q, Inv G z ∧ ∀ s, ∀ p ∈ G.Y, R + 1 < Φ s p → (G.dOm q z).1 s p = (w 0).1 s p

def GeoRet : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d),
    IsCone G.Y → ∀ l : S → V → ℝ, G.IsInvGauge l → ∀ Φ : S → V → ℝ, IsFun G Φ → ∀ (R : ℝ) (q : ℕ) (w : G.Om (q + 1))
    (z : G.Om q), G.dOm (q + 1) w = 0 → (∀ s, RadBasic G.Y (w.1 s)) → Inv G z →
    (∀ s, ∀ p ∈ G.Y, R < Φ s p → (G.dOm q z).1 s p = w.1 s p) →
    ∃ z' : G.Om q, Good G z' ∧ ∀ s, ∀ p ∈ G.Y, R < Φ s p → (G.dOm q z').1 s p = w.1 s p

def LamEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∃ lam : GA E a → ℝ, IsLam lam

def DescEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∃ Φ, Desc U f Φ

def DescFun : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∀ Φ, Desc U f Φ → IsFun (geo ho U Ξ) Φ

def SecOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ τ : HV E a → GL (Fin a) (Cinf E), τ (hOne E a) = 1 ∧
    ContDiffAt ℝ ∞ (fun p => toL (τ p).val) (hOne E a) ∧ ContDiffAt ℝ ∞ (fun p => toL ((τ p)⁻¹).val) (hOne E a) ∧
    ContDiffAt ℝ ∞ (fun p => sand (τ p)) (hOne E a) ∧ ContDiffAt ℝ ∞ (fun p => sand (τ p)⁻¹) (hOne E a) ∧
    ∀ᶠ p in 𝓝 (hOne E a), sand (τ p) (hOne E a) = p

def LocBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∀ p₀ ∈ cone E a, ∃ c : ℝ, ∀ᶠ p in 𝓝 p₀,
    ∃ h : GL (Fin a) (Cinf E), Bnd c h ∧ sand h (hOne E a) = p

def ChartSz : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (k : ℕ) (ρ : GA E a → ℝ), (∀ g, 0 ≤ ρ g) → ∀ φ : Sm E a,
    (∀ l : List (Lie E a), ∃ C : ℝ, ∀ g, ‖((l.map (lie E a)).prod φ).1 g‖ ≤ C * ρ g) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, Sz k (chart φ.1 g) (oneL E a) (C * ρ g)

def ZwSz : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ W, FCorr U Y W → ∀ k : ℕ, ∃ c : ℝ, ∀ g x, Sz k (Zw U W g x) (hOne E a) c

def RapidEig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (r : ℝ), HasOne Ξ r → ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)),
    lie E a (oneL E a) ((l.map (lie E a)).prod (Bor.cmp j (α X))) = -(r : ℂ) • (l.map (lie E a)).prod (Bor.cmp j (α X)) ∧
    ∀ g, ev ((l.map (smA Ξ)).prod (α X)) g j = ((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g

def RapidAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f lam : GA E a → ℝ) (C : ℝ), IsLam lam → (∀ g, f g ≤ C * (1 + Real.log (qht g))) →
    ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → RapidD α → ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 ≤ A →
      ∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)), ∃ M : ℝ, ∀ g,
        ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g‖ ≤ M * Real.exp (B * |lam g| - A * f g)

def CorrForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (v : Fin q → HV E a),
    ∃ (ι : Type) (_ : Fintype ι) (X : ι → Fin q → Herm E a) (j : ι → Fin Ξ.d) (Θ : ι → HV E a → Fin Ξ.d → ℂ)
      (τ : HV E a → Lie E a), τ (hOne E a) = oneL E a ∧ ContDiffAt ℝ ∞ τ (hOne E a) ∧ (∀ i, ContDiffAt ℝ ∞ (Θ i) (hOne E a)) ∧
      ∀ (U : Subgroup (GL (Fin a) (Af E))) (α : Co Ξ q) (w : Fm U Ξ q), Corr U Ξ α w → ∀ g x,
        (fun p => Tw U Ξ w g x p v) =ᶠ[𝓝 (hOne E a)] fun p => ∑ i, chart (Bor.cmp (j i) (α (X i))).1 (pt g x) (τ p) • Θ i p

def CorrSz : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ) (α : Co Ξ q) (w : Fm U Ξ q), Corr U Ξ α w → ∀ ρ : GA E a → ℝ, (∀ g, 0 ≤ ρ g) →
    (∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)), ∃ M : ℝ, ∀ g,
      ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g‖ ≤ M * ρ g) →
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ g x, Sz k (Tw U Ξ w g x) (hOne E a) (M * ρ (pt g x))

def TwOps : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a), IsFlow (geo ho U Ξ) W → ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
    IsField (cone E a) (Zw U W g x) ∧ (∀ t p, flow (Zw U W g x) t p = sand g⁻¹ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) t (sand g p))) ∧
    ∀ q : ℕ, (∀ w : (geo ho U Ξ).Om q, ContDiffOn ℝ ∞ (Tw U Ξ w.1 g x) (cone E a) ∧ ∀ p ∈ cone E a,
        Tw U Ξ (pbOm (geo ho U Ξ) W w).1 g x p = pb (flow (Zw U W g x) 1) (Tw U Ξ w.1 g x) p) ∧
      ∀ w : (geo ho U Ξ).Om (q + 1), ∀ p ∈ cone E a,
        Tw U Ξ (homOm (geo ho U Ξ) W w).1 g x p = hom (Zw U W g x) (Tw U Ξ w.1 g x) p

def Move : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q k : ℕ) (c : ℝ), ∃ D : ℝ, 0 ≤ D ∧ ∀ (w : (geo ho U Ξ).Om q) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (h : GL (Fin a) (Cinf E)) (b : ℝ), Bnd c h →
      Sz k (Tw U Ξ w.1 (g * h) x) (hOne E a) b → Sz k (Tw U Ξ w.1 g x) (sand h (hOne E a)) (D * b)

def DecP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∀ W, FCorr U Y W → ∀ lam, IsLam lam →
    ∀ (q k : ℕ) (B : ℝ), 0 ≤ B → ∃ D : ℝ, 0 ≤ D ∧ ∀ A M : ℝ, 0 ≤ A → 0 ≤ M → ∀ w : (geo ho U Ξ).Om q,
      Dec U Ξ f lam f₀ k A B M w.1 → Dec U Ξ f lam f₀ k A B (D * Real.exp (-(A * c)) * M) (pbOm (geo ho U Ξ) W w).1

def DecK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∀ W, FCorr U Y W → ∀ lam, IsLam lam →
    ∀ (q k : ℕ) (A B : ℝ), 0 ≤ A → 0 ≤ B → ∃ D : ℝ, 0 ≤ D ∧ ∀ M : ℝ, 0 ≤ M → ∀ w : (geo ho U Ξ).Om (q + 1),
      Dec U Ξ f lam f₀ k A B M w.1 → Dec U Ξ f lam (f₀ + C) k A B (D * M) (homOm (geo ho U Ξ) W w).1

def Loc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f lam : GA E a → ℝ), (∀ g, 0 ≤ f g) → IsLam lam → ∀ Φ, Desc U f Φ → IsFun (geo ho U Ξ) Φ →
    ∀ (q k : ℕ) (A B R : ℝ), 0 ≤ A → 0 ≤ B → ∀ s, ∀ p ∈ cone E a, R < Φ s p → ∃ N ∈ 𝓝 p, ∃ D : ℝ,
      ∀ M : ℝ, 0 ≤ M → ∀ w : (geo ho U Ξ).Om q, Dec U Ξ f lam R k A B M w.1 → ∀ x ∈ N, Sz k (w.1 s) x (D * M)

def Supp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∀ Φ, Desc U f Φ → ∀ (q : ℕ) (α : Co Ξ q) (w : Fm U Ξ q) (R : ℝ), Corr U Ξ α w →
    (∀ s, ∀ p ∈ cone E a, R < Φ s p → w s p = 0) → CSupp α

end UpperTheory.V.Lit.Geo.Cs
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CutBd
section
open UpperTheory.V.Lit.Geo

private theorem aux {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {q : ℕ} (A : F) (u : ℂ) (l : Fin (q + 1) → ℂ)
    (B : Fin (q + 1) → F) (n : Fin (q + 1) → ℝ) (s b M M' : ℝ) (hn : ∀ i, 0 ≤ n i) (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hs : ‖1 - u‖ ≤ s) (hl : ∀ i, ‖l i‖ ≤ b * n i)
    (hB : b = 0 ∨ ∀ i, ‖B i‖ ≤ M * ∏ j, n (i.succAbove j)) (hA : ‖A‖ ≤ M' * ∏ i, n i) :
    ‖A - (u • A + ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i)‖ ≤ (s * M' + (q + 1) * b * M) * ∏ i, n i := by
  have hP : 0 ≤ ∏ i, n i := Finset.prod_nonneg fun i _ => hn i
  have e : A - (u • A + ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i) =
      (1 - u) • A - ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i := by
    rw [sub_smul, one_smul, sub_sub]
  have h1 : ‖(1 - u) • A‖ ≤ s * (M' * ∏ i, n i) := by
    rw [norm_smul]
    exact mul_le_mul hs hA (norm_nonneg _) ((norm_nonneg _).trans hs)
  have h2 : ∀ i : Fin (q + 1), ‖((-1 : ℂ) ^ (i : ℕ) * l i) • B i‖ ≤ b * M * ∏ i, n i := fun i => by
    rw [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rcases hB with h | h
    · have h0 : ‖l i‖ = 0 := le_antisymm (by simpa [h] using hl i) (norm_nonneg _)
      simp [h, h0]
    · refine (mul_le_mul (hl i) (h i) (norm_nonneg _) (mul_nonneg hb (hn i))).trans_eq ?_
      rw [Fin.prod_univ_succAbove n i]
      ring
  have h3 : ‖∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i‖ ≤ (q + 1) * (b * M * ∏ i, n i) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => h2 i).trans_eq ?_)
    simp
  rw [e]
  refine (norm_sub_le _ _).trans ((add_le_add h1 h3).trans_eq ?_)
  ring

theorem UpperTheory.V.Lit.Geo.cutBd :
    CutBd := by
  intro E _ _ _ a Ξ q u η ζ h g s b M M' hM _ hb hs hl hη hd X
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, h]
  exact aux _ _ _ _ (fun i => ‖UpperTheory.V.Lit.Dr.hv (X i)‖) s b M M' (fun _ => norm_nonneg _) hM hb hs
    (fun i => hl _) (hη.imp id fun hη i => hη _) (hd X)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtDiv
section
open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Pf
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def ptForm (χ : HChar E) (g : GA E a) : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun φ ψ => starRingEnd ℂ ((mulChi a χ φ).1 g) * (mulChi a χ ψ).1 g)
    (fun φ φ' ψ => by simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, add_mul])
    (fun c φ ψ => by simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc])
    (fun φ ψ ψ' => by simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, mul_add])
    (fun c φ ψ => by
      simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

private theorem ptForm_apply (χ : HChar E) (g : GA E a) (φ ψ : Sm E a) :
    ptForm χ g φ ψ = starRingEnd ℂ ((mulChi a χ φ).1 g) * (mulChi a χ ψ).1 g := rfl

private theorem pt_tform (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    pt χ G x y g = tform (ptForm χ g) G x y := by
  rw [(ptInv E a χ d G x y).1 g, tform_apply]
  rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

private theorem sum_val {ι : Type} (s : Finset ι) (f : ι → Sm E a) (g : GA E a) :
    (∑ i ∈ s, f i).1 g = ∑ i ∈ s, (f i).1 g := by
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Lit.Geo.Pf.ptDiv :
    UpperTheory.V.Lit.Geo.Pf.PtDiv := by
  intro E _ _ _ a Ξ r χ G hχ hG x y
  choose θ h0 h1 using fun i j => prodEx E a (mulChi a χ (cmp i x)) (mulChi a χ (cmp j y))
  refine ⟨∑ i, ∑ j, G i j • θ i j, fun g => ?_, fun X g => ?_⟩
  · rw [(ptInv E a χ _ G x y).1 g]
    simp only [sum_val, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h0]
  · set c : ℂ := ((r * ell E a (toL X.1) : ℝ) : ℂ) with hc
    have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
    have hX : star X.1 = X.1 := X.2
    have e1 := (UpperTheory.V.Lit.Bor.tformAdj (Sm E a) Ξ.d (ptForm χ g) ⊤ G (Ξ.dmat (toL X.1)) (Ξ.dmat (toL X.1)) 0 0).1
      (by have := hG.adj X.1; rwa [hX] at this) x y
    have e3 : smLie Ξ (toL X.1) y = smA Ξ (toL X.1) y + smB Ξ (toL X.1) y := by
      simp [smB]
    have e4 : smAdj Ξ r (toL X.1) x = smB Ξ (toL X.1) x - smA Ξ (toL X.1) x - (2 * c) • x := by
      rw [smAdj, adj_apply, ← algebraMap_smul ℂ (2 * r * ell E a (toL X.1)) x]
      congr 2
      rw [hc]
      simp [mul_assoc]
    have e5 : (lie E a (toL X.1) (∑ i, ∑ j, G i j • θ i j)).1 g =
        tform (ptForm χ g) G x (smA Ξ (toL X.1) y) + tform (ptForm χ g) G (smA Ξ (toL X.1) x) y +
          2 * c * tform (ptForm χ g) G x y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, sum_val, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h1, tform_apply,
        smA_apply, cmp_rT, Finset.mul_sum, ← Finset.sum_add_distrib, ptForm_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hχ.2, hχ.2, ← hc]
      simp only [map_add (f := _), map_smul, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        map_mul, hcc]
      ring
    rw [e5, pt_tform, pt_tform, e3, e4, smB_apply]
    simp only [map_add (f := _), map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, e1,
      map_mul, hcc, map_ofNat]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PtRetr
section
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.ptRetr :
    PtRetr := by
  intro E _ _ _ a ha U hU Ξ r χ G n e hD q α β hα hβ g
  have hv := Pf.levInv E a ha U hU Ξ r χ hD.one hD.tw
  obtain ⟨t, ht⟩ := (retrFacts E a).1 g
  obtain ⟨s, hs⟩ := hD.tw.1
  have h1 := Pf.chiOne E a χ s hs (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g)
  rw [Pf.ptIp_eq]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hc := ((Pf.ptInv E a χ _ G _ _).2.1 (hv q α hα fun i => e (I i)) (hv q β hβ fun i => e (I i))).centre t g
  rw [← hc, ← ht, Pf.pt, h1]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullCorrBd
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.corrBd :
    CorrBd := by
  intro E _ _ _ a U Ξ C q
  obtain ⟨B, hB, hM⟩ := matBd E a Ξ C
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  obtain ⟨T, hT⟩ := (retrFacts E a).2.2 C
  refine ⟨B * Real.exp (|r| * T) * B ^ q, by positivity, ?_⟩
  intro α w hα hw g y h x M hg h1 h2 hM0 hbd v
  obtain ⟨m1, -, m3⟩ := hM h h1 h2
  obtain ⟨t, ht, e⟩ := hT g h h1 h2
  have hcomm : infGL E a h * finGL E a x = finGL E a x * infGL E a h := by
    first | exact GlobalTheory.CuspRep.infGL_comm _ _ | exact TR.infGL_comm _ _
  rw [hg, mul_assoc, ← hcomm, ← mul_assoc, ← map_mul] at e
  set X : Fin q → Herm E a := fun i => hv.symm ((1 / 2 : ℝ) • sand h⁻¹ (v i)) with hX
  have hc := hw (y * h) x X
  have hv' : (fun i => (2 : ℝ) • sand (y * h) (hv (X i))) = fun i => sand y (v i) := by
    funext i
    simp only [hX, LinearEquiv.apply_symm_apply, map_smul, smul_smul]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
    norm_num
  have hcv := centreVal E a U Ξ r hr q α hα X 1 t
    (GroundTheory.Automorphic.CuspidalSpectrum.retractOne (g * infGL E a h) : KernelIndexFullLattice.G1 E a).1
  rw [map_one, one_mul] at hcv
  rw [hv', e, hcv] at hc
  rw [hc, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_left]
  refine (m1 _).trans ?_
  rw [norm_smul]
  have hexp : ‖Complex.exp (-(r * t))‖ ≤ Real.exp (|r| * T) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have : (-((r : ℂ) * t)).re = -(r * t) := by simp
    rw [this]
    refine (neg_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have hp : ∏ i, ‖hv (X i)‖ ≤ B ^ q * ∏ i, ‖v i‖ := by
    have : B ^ q * ∏ i, ‖v i‖ = ∏ i, B * ‖v i‖ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [this]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    simp only [hX, LinearEquiv.apply_symm_apply]
    rw [norm_smul]
    have h3 := m3 (v i)
    have h4 := norm_nonneg (sand h⁻¹ (v i))
    have h5 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [h5]
    linarith
  have hb := (hbd X).trans (mul_le_mul_of_nonneg_left hp hM0)
  calc _ ≤ B * (Real.exp (|r| * T) * (M * (B ^ q * ∏ i, ‖v i‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hexp hb (norm_nonneg _) (Real.exp_pos _).le) hB
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmApply
section
open UpperTheory.V.Lit.Geo
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.omApply :
    OmApply := by
  intro Γ V S _ _ _ _ d G W hW q
  refine ⟨fun w s p hp => ?_, fun w s p hp => ?_⟩
  · refine toOm_apply G (z := fun s => pb (flow (W s) 1) (w.1 s)) (fun s x hx => ?_) s hp
    have hx' : flow (W s) 1 x ∈ G.Y := (hW.field s).2 x hx 1 ⟨zero_le_one, le_rfl⟩
    have h1 : ContDiffAt ℝ ∞ (W s) x := (hW.field s).1.contDiffAt (G.isOpen.mem_nhds hx)
    have h2 : ContDiffAt ℝ ∞ (flow (W s) 1) x := contDiffAt_id.add (h1.const_smul (1 : ℝ))
    have h3 : ContDiffAt ℝ ∞ (w.1 s) (flow (W s) 1 x) := (w.2 s).1.contDiffAt (G.isOpen.mem_nhds hx')
    exact (pbD V V (Fin d → ℂ) q _ _ x h2 h3).1.contDiffWithinAt
  · exact toOm_apply G (z := fun s => hom (W s) (w.1 s))
      (fun s => (hkSmooth V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) q (w.1 s) (w.2 s).1).2.2.2) s hp
end

