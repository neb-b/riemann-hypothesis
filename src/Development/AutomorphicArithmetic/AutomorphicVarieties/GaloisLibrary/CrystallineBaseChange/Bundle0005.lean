module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0064
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.ReductionIwasawa
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CoRatAff
section
open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Sd UpperTheory.V.Sd.Eis

private theorem co_aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) :
    aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem co_rat_aff (F : Type) [Field F] [NumberField F] (a : Fˣ) (y : F) :
    ratGL F 2 (aff a y) =
      aff (Units.map (algebraMap F (Ad F)).toMonoidHom a) (algebraMap F (Ad F) y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, ratGL]

theorem UpperTheory.V.Br.ctOne :
    UpperTheory.V.Br.CtOne := by
  intro F _ _
  obtain ⟨h1, h2, h3, h4, -, -, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock F
  letI iM : MeasurableSpace (UPos 2 1 → AdeleRing (𝓞 F) F) := MeasurableSpace.pi
  have hμ : (unipMeasure F 2 1).IsAddHaarMeasure := inferInstance
  have hB : BorelSpace (UPos 2 1 → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have hL : ratN F 2 1 = unipLattice F 2 1 := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  have hF : IsAddFundamentalDomain (ratN F 2 1) (unipFundamentalDomain F 2 1) (unipMeasure F 2 1) := by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain
  have main : ∀ [MeasurableSpace (NA F)] [BorelSpace (NA F)] (ν : Measure (NA F)) [ν.IsAddHaarMeasure] (D₀ : Set (NA F)),
      IsAddFundamentalDomain (ratN F 2 1) D₀ ν → ∀ φ : GA F 2 → ℂ, (∀ γ g, φ (ratGL F 2 γ * g) = φ g) →
      (∀ g, cterm ν D₀ φ g = 0) → GlobalTheory.CuspRep.IsCuspidal φ := by
    intro j1 j2 ν _ D₀ hD₀ φ hl h0 r hr0 hr1 i1 i2 μ D hμ' hD g
    obtain rfl : r = 1 := by omega
    obtain rfl : i1 = j1 :=
      (@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ j1 j2).symm
    have hper : ∀ γ ∈ ratN F 2 1, ∀ x : NA F, φ (unip (γ + x) * g) = φ (unip x * g) := by
      rintro _ ⟨y, rfl⟩ x
      rw [hx, hx x]
      refine Eq.trans ?_ (hl (aff 1 (y ⟨(0, 1), by decide⟩)) _)
      rw [← mul_assoc, co_rat_aff, co_aff_mul, map_one, one_mul, Units.val_one, one_mul, add_comm (x _)]
      rfl
    have hD' : IsAddFundamentalDomain (ratN F 2 1) D ν := hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
    have h : ∫ x in D, φ (unip x * g) ∂ν = 0 :=
      (hD'.setIntegral_eq hD₀ (f := fun x => φ (unip x * g)) fun γ x => hper γ γ.2 x).trans (h0 g)
    rw [Measure.isAddLeftInvariant_eq_smul μ ν, Measure.restrict_smul, integral_smul_nnreal_measure, h, smul_zero]
  exact ⟨iM, hB, unipMeasure F 2 1, hμ, unipFundamentalDomain F 2 1, hF, @main iM hB _ hμ _ hF⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.IwasawaA
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GroundTheory.Automorphic
open scoped Matrix

private theorem upper_eq {R : Type} [CommRing R] (b : GL (Fin 2) R) (h : b 1 0 = 0) (h0 : IsUnit (b 0 0)) (h1 : IsUnit (b 1 1)) :
    ∃ (z y : Rˣ) (x : R), b = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y x := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨d, hd⟩ := h1
  refine ⟨d, d⁻¹ * a, (d⁻¹ : Rˣ) * b 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.scalar, h, ← ha, ← hd]

private theorem orth {E : Type} [NormedField E] (φ : E ≃+* ℝ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (k : Matrix (Fin 2) (Fin 2) E)
    (hk : ∀ y : Fin 2 → E, Reduction.euclidNorm (y ᵥ* k) = Reduction.euclidNorm y) (i j : Fin 2) :
    φ (k i 0) * φ (k j 0) + φ (k i 1) * φ (k j 1) = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  have h : ∀ s t : E, (φ s * φ (k 0 0) + φ t * φ (k 1 0)) ^ 2 + (φ s * φ (k 0 1) + φ t * φ (k 1 1)) ^ 2 = φ s ^ 2 + φ t ^ 2 := by
    intro s t
    have := hk ![s, t]
    unfold Reduction.euclidNorm at this
    rw [Real.sqrt_inj (by positivity) (by positivity)] at this
    simpa [← hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using this
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  simp only [map_one, map_zero] at h1 h2 h3
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith

theorem UpperTheory.V.Br.iwasawaA :
    UpperTheory.V.Br.IwasawaA := by
  intro F _ _ _ g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  obtain ⟨z, y, x, hz⟩ := upper_eq b (hb (show (0 : Fin 2) < 1 by decide))
    (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 0) (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1)
  have hr : ((Matrix.GeneralLinearGroup.map (TR.pInf F) k : GL (Fin 2) (TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) ∈
      Matrix.unitaryGroup (Fin 2) (TR.Rinf F) := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j w
    have := orth (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w))
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
        (map_zero _) x) _ (hk.1 w) i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine Eq.trans this ?_
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  have hu : Matrix.GeneralLinearGroup.map (pFin F) k ∈ AdelicGLn.integralFiniteGL F 2 :=
    (AdelicGLn.mem_integralFiniteGL_iff_forall F 2).2 hk.2
  obtain ⟨hu1, hu2⟩ := (AdelicGLn.mem_integralFiniteGL_iff F 2).1 hu
  refine ⟨z, y, x, ⟨_, hr⟩, Matrix.GeneralLinearGroup.map (pFin F) k, ?_, ?_⟩
  · refine mem_KLev.2 ⟨fun a c => mem_Ohat.2 (hu1 a c), fun a c => mem_Ohat.2 (hu2 a c), fun a c => ⟨_, ?_, by rw [Nat.cast_one, one_mul]⟩⟩
    refine sub_mem (mem_Ohat.2 (hu1 a c)) ?_
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · have e : Unitary.toUnits (⟨_, hr⟩ : TR.Kinf F 2) = Matrix.GeneralLinearGroup.map (TR.pInf F) k := Units.ext rfl
    rw [e, TR.infGL_mul_finGL, ← hz]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial MeasureTheory
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Br

structure IsLow (k : ℕ) (φ : TR.Sm ℚ 2) : Prop where
  wt : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ
  low : ∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)
  one : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0

def CapTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (v : InfinitePlace F) (a b : ℂ), π.HasInfChar v {a, b} →
    ∀ φ ∈ π.V, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = (a + b) • φ ∧
      TR.Eop v 0 0 (TR.Eop v 0 0 φ) + TR.Eop v 0 1 (TR.Eop v 1 0 φ) + TR.Eop v 1 0 (TR.Eop v 0 1 φ) + TR.Eop v 1 1 (TR.Eop v 1 1 φ) =
        (a ^ 2 + b ^ 2 - 1 / 2) • φ

def WtVec : Prop :=
  ∀ π : TR.CuspSub ℚ 2, ∃ φ ∈ π.V, φ ≠ 0 ∧ ∃ n : ℤ, ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * n) • φ

def Sl2Low : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W R L : Module.End ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (k : ℕ), 3 ≤ k →
    W * R - R * W = (2 : ℂ) • R → W * L - L * W = (-2 : ℂ) • L → (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W) →
    (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - (W * W + (2 : ℂ) • W) →
    (∀ x, H x x = 0 → x = 0) → (∀ x y, H (W x) y = H x (W y)) → (∀ x y, H (R x) y = -H x (L y)) → (∀ x y, H (L x) y = -H x (R y)) →
    (∃ x, x ≠ 0 ∧ ∃ n : ℤ, W x = (n : ℂ) • x) →
    ∃ x, x ≠ 0 ∧ ((W x = (k : ℂ) • x ∧ L x = 0) ∨ (W x = (-(k : ℂ)) • x ∧ R x = 0))

def HolVec : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ π : TR.CuspSub ℚ 2, (∀ v, π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}) →
    ∀ H, Gk.IsHerm π H → ∃ φ ∈ π.V, φ ≠ 0 ∧ IsLow k φ

def LevelVec : Prop :=
  ∀ (k : ℕ) (π : TR.CuspSub ℚ 2), (∃ φ ∈ π.V, φ ≠ 0 ∧ IsLow k φ) →
    ∃ (N : ℕ) (ψ : DirichletCharacter ℂ N) (ν : HChar ℚ), 1 ≤ N ∧ IsDirOf ψ ν ∧
      ∃ φ ∈ (π.twist ν).V, φ ≠ 0 ∧ IsLow k φ ∧ ∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ

def CharOf : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (ω : HChar ℚ) (φ : TR.Sm ℚ 2), φ ≠ 0 → (∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) →
    (∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ) →
    (∀ (z : Ideles ℚ) (g : GA ℚ 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
    ∃ χ : DirichletCharacter ℂ N, IsDirOf χ ω

def down (k : ℕ) (φ : GA ℚ 2 → ℂ) (z : ℍ) : ℂ :=
  ((z.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * φ (upR (aff (Units.mk0 z.im z.im_pos.ne') z.re))

def DownLift : Prop :=
  ∀ (k N : ℕ), 1 ≤ N → ∀ φ : TR.Sm ℚ 2, (∀ γ g, φ.1 (ratGL ℚ 2 γ * g) = φ.1 g) → IsLow k φ → (∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ) →
    Nf.IsLift k N (down k φ.1) φ.1

def DownHol : Prop := ∀ (k : ℕ) (φ : TR.Sm ℚ 2), IsLow k φ → MDiff (down k φ.1)

def DownChar : Prop :=
  ∀ (k N : ℕ), 1 ≤ N → ∀ (χ : DirichletCharacter ℂ N) (ω : HChar ℚ), IsDirOf χ ω → ∀ (f : ℍ → ℂ) (φ : GA ℚ 2 → ℂ), Nf.IsLift k N f φ →
    (∀ (z : Ideles ℚ) (g : GA ℚ 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g) → HasChar k χ f

def PerZero : Prop :=
  ∀ (f : ℍ → ℂ) (N : ℕ), 0 < N → MDiff f → (∀ z : ℍ, f ((N : ℝ) +ᵥ z) = f z) →
    (∃ (C : ℝ) (m : ℕ), ∀ z : ℍ, 1 ≤ z.im → |z.re| ≤ N → ‖f z‖ ≤ C * z.im ^ m) →
    (∀ z : ℍ, ∫ t in (0 : ℝ)..N, f (t +ᵥ z) = 0) → IsZeroAtImInfty f

def CuspMean : Prop :=
  ∀ φ : TR.Sm ℚ 2, TR.IsCuspForm φ → ∀ g, ∃ N : ℕ, 0 < N ∧ ∀ y : GL (Fin 2) ℝ,
    Function.Periodic (fun t : ℝ => φ.1 (upR (aff 1 t) * (g * upR y))) N ∧ ∫ t in (0 : ℝ)..N, φ.1 (upR (aff 1 t) * (g * upR y)) = 0

def DownZero : Prop := ∀ (k : ℕ) (φ : TR.Sm ℚ 2), TR.IsCuspForm φ → IsLow k φ → IsZeroAtImInfty (down k φ.1)

def Deadel : Prop :=
  ∀ (k N : ℕ), 1 ≤ N → ∀ (χ : DirichletCharacter ℂ N) (ω : HChar ℚ), IsDirOf χ ω → ∀ φ : TR.Sm ℚ 2, TR.IsCuspForm φ → IsLow k φ →
    (∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ) →
    (∀ (z : Ideles ℚ) (g : GA ℚ 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
    ∃ f : CuspForm (Gamma1 N) (k : ℤ), HasChar k χ f ∧ Nf.IsLift k N f φ.1

def UOfSat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (x : V) (α β : ℂˣ), GlobalTheory.LFun.IsSatVecGL w ρ x {α, β} →
    Uop w ρ 0 x = ((((normV w : ℝ) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * ((α : ℂ) + β)) • x ∧
    ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((α * β : ℂˣ) : ℂ) • x

def EigOf : Prop :=
  ∀ (k N : ℕ), 1 ≤ k → 1 ≤ N → ∀ (χ : DirichletCharacter ℂ N) (ω : HChar ℚ), IsDirOf χ ω → ∀ (f : CuspForm (Gamma1 N) (k : ℤ))
    (φ : TR.Sm ℚ 2), Nf.IsLift k N f φ.1 → IsHol k (lev N) ω φ → ∀ (w : Pl ℚ) (α β : ℂˣ), ¬ normV w ∣ N →
    GlobalTheory.LFun.IsSatVecGL w (locSm ℚ w) φ {α, β} →
    IsEigAt k χ f (normV w) ((((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β)) ∧ ((α * β : ℂˣ) : ℂ) = χ (normV w : ZMod N)

def EigEx : Prop :=
  ∀ (N k : ℕ) [NeZero N], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) (k : ℤ)), HasChar k χ f → f ≠ 0 → ∀ a : ℕ → ℂ,
    ∃ g : Eigenform k N χ, ∀ p : ℕ, p.Prime → IsEigAt k χ f p (a p) → g.a p = a p

def ClTwist : Prop :=
  ∀ (N k : ℕ) [NeZero N] (χ ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) (k : ℤ)), HasChar k χ f →
    ∃ g : CuspForm (Gamma1 (N * N)) (k : ℤ), HasChar k (DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ ^ 2)) g ∧
      ∀ n : ℕ, coef g n = ψ (n : ZMod N) * coef f n

def MinNew : Prop :=
  ∀ (N k : ℕ) [NeZero N], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ),
    ∃ (f : Newform k) (_ : NeZero f.M) (h : Eigenform k f.M f.χ), h.f = f.f ∧ ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → h.a p = g.a p

def CharEq : Prop :=
  ∀ (k N M : ℕ) [NeZero N] [NeZero M], 2 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (g : Eigenform k N χ)
    (h : Eigenform k M ψ), (∀ᶠ p : ℕ in Filter.cofinite, p.Prime → h.a p = g.a p) →
    ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → χ (p : ZMod N) = ψ (p : ZMod M)

def RepEig : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ π : TR.CuspSub ℚ 2, (∀ v, π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}) →
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ), ∀ᶠ w : Pl ℚ in Filter.cofinite, ∃ α β : ℂˣ,
      π.HasSat w {α, β} ∧ g.a (normV w) = (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) ∧
        ((α * β : ℂˣ) : ℂ) = χ (normV w : ZMod N)

def RepNewAE : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (j : ℤ) (π : TR.CuspSub ℚ 2), (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) →
    ∃ f : Newform k, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ B, π.HasSat w B ∧
      ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod = f.heckePoly (normV w)

end UpperTheory.V.Br
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RotEig
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V

namespace UpperTheory.V.Br.RotationEigenvalues

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

omit [NumberField F] in
private theorem rot_add (θ η : TR.Rinf F) : rot (θ + η) = rot θ * rot η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
private theorem rot_zero : rot (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

variable [IsTotallyReal F]

private theorem rot_eig (φ : TR.Sm F 2) (z : ℂ) (h : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ) (g : GA F 2) (θ : TR.Rinf F) :
    φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot θ))) = Complex.exp (z * ∑ v, (θ v : ℂ)) * φ.1 g := by
  classical
  set μ : ℂ := z * ∑ v, (θ v : ℂ) with hμ
  let X : TR.Lie F 2 := TR.toL !![0, θ; -θ, 0]
  have hX : X = ∑ v, θ v • (TR.toL (Matrix.single 0 1 (Pi.single v 1)) - TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [X, Finset.sum_apply, Pi.single_apply]
  have hL : TR.lie F 2 X φ = μ • φ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hX, map_sum, LinearMap.sum_apply, hμ, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, Complex.coe_smul, ← h v]
    simp only [TR.Eop]
  have hc : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (t • θ))).val) X 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    have h1 : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
    fin_cases i <;> fin_cases j
    · simpa [X, rot] using h1.cos
    · simpa [X, rot] using h1.sin
    · simpa [X, rot] using h1.sin.fun_neg
    · simpa [X, rot] using h1.cos
  let f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ))))
  have hf : ∀ t, HasDerivAt f (μ * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ)))) (fun s => Unitary.toUnits (rot (s • θ))) X
      (by rw [zero_smul, rot_zero, map_one]) hc
    rw [← TR.lie_apply, hL] at h1
    have h2 : HasDerivAt (fun s => f (t + s)) (μ * f t) 0 := by
      simpa only [f, add_smul, rot_add, map_mul, mul_assoc] using! h1
    have h3 := HasDerivAt.comp_sub_const t t (f := fun s => f (t + s)) (by rw [sub_self]; exact h2)
    simpa using h3
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-μ * s) * f s) 0 t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => -μ * (s : ℂ)) (-μ) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-μ)
    exact (h1.cexp.fun_mul (hf t)).congr_deriv (by ring)
  have h4 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, one_smul, zero_smul, rot_zero, map_one, mul_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul] at h4
  rw [← h4, ← mul_assoc, ← Complex.exp_add]
  simp

end UpperTheory.V.Br.RotationEigenvalues

open UpperTheory.V.Br.RotationEigenvalues in
theorem UpperTheory.V.Br.rotEig :
    UpperTheory.V.Br.RotEig := by
  intro F _ _ _ φ z hφ θ h hh g
  have e : h = Unitary.toUnits (rot θ) := Units.ext hh
  rw [e]
  exact rot_eig φ z hφ g θ
end

