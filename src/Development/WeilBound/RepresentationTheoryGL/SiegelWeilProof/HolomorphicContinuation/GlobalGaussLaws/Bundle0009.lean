module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseA

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DecH

variable {n : ℕ}

def mkGR (M : M2 n) (hu : IsUnit M.det) (hg : InG M) : GR n := ⟨M.nonsingInvUnit hu, hg⟩

theorem mR_mkGR (M : M2 n) (hu : IsUnit M.det) (hg : InG M) : mR (mkGR M hu hg) = M := rfl

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hb]

theorem inG_nbar {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (nbar c) := by
  unfold InG nbar JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc]

theorem inG_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : InG (mM a) := by
  have hu : IsUnit aᴴ.det := by
    rw [det_conjTranspose]
    exact ha.star
  unfold InG mM JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [conjTranspose_nonsing_inv, mul_nonsing_inv _ hu, nonsing_inv_mul _ ha]

theorem det_nU (b : Matrix (Fin n) (Fin n) ℂ) : (nU b).det = 1 := by
  simp [nU, det_fromBlocks_zero₂₁]

theorem det_nbar (c : Matrix (Fin n) (Fin n) ℂ) : (nbar c).det = 1 := by
  simp [nbar, det_fromBlocks_zero₁₂]

theorem isUnit_det_mM {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : IsUnit (mM a).det := by
  have hu : IsUnit aᴴ.det := by
    rw [det_conjTranspose]
    exact ha.star
  unfold mM
  rw [det_fromBlocks_zero₂₁]
  exact ha.mul (isUnit_nonsing_inv_det _ hu)

end PositivityTheory.Rg.Sw.Glob.DecH

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.DecH

theorem decomp : Decomp := by
  intro n y
  have hmul : ∀ {X Y : M2 n}, InG X → InG Y → InG (X * Y) := by
    intro X Y hX hY
    unfold InG at *
    rw [conjTranspose_mul]
    calc Yᴴ * Xᴴ * JJ n * (X * Y) = Yᴴ * (Xᴴ * JJ n * X) * Y := by
          simp only [Matrix.mul_assoc]
      _ = JJ n := by rw [hX, hY]
  have hg : InG (mR y) := y.2
  have hdet : IsUnit (mR y).det := Matrix.isUnits_det_units (y : GL (Fin n ⊕ Fin n) ℂ)
  obtain ⟨A, B, C, D, e⟩ : ∃ A B C D : Matrix (Fin n) (Fin n) ℂ, mR y = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  rw [e] at hg hdet
  obtain ⟨t, ht⟩ := exists_real_det_ne_zero (det_sub_I_smul_ne_zero hg hdet)
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = A - (t : ℂ) • C := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q = B - (t : ℂ) • D := ⟨_, rfl⟩
  rw [← hP] at ht
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr ht
  have hPHu : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]
    exact hPu.star
  have hshift : nU ((-(t : ℂ)) • 1) * fromBlocks A B C D = fromBlocks P Q C D := by
    unfold nU
    rw [fromBlocks_multiply]
    simp [hP, hQ, sub_eq_add_neg]
  have hG : InG (fromBlocks P Q C D) := by
    rw [← hshift]
    exact hmul (inG_nU (by simp)) hg
  obtain ⟨r1, -, -⟩ := inG_blocks hG
  obtain ⟨s1, -, s3, -⟩ := inG_blocks_dual hG
  have hb : (P⁻¹ * Q)ᴴ = P⁻¹ * Q := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Qᴴ * Pᴴ⁻¹ = P⁻¹ * (P * Qᴴ) * Pᴴ⁻¹ := by
          rw [← Matrix.mul_assoc P⁻¹, nonsing_inv_mul _ hPu, Matrix.one_mul]
      _ = P⁻¹ * (Q * Pᴴ) * Pᴴ⁻¹ := by rw [s1]
      _ = P⁻¹ * Q := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hPHu, Matrix.mul_one]
  have hc : (C * P⁻¹)ᴴ = C * P⁻¹ := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Pᴴ⁻¹ * Cᴴ = Pᴴ⁻¹ * (Cᴴ * P) * P⁻¹ := by
          rw [Matrix.mul_assoc (Pᴴ⁻¹), Matrix.mul_assoc Cᴴ, mul_nonsing_inv _ hPu, Matrix.mul_one]
      _ = Pᴴ⁻¹ * (Pᴴ * C) * P⁻¹ := by rw [r1]
      _ = C * P⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hPHu, Matrix.one_mul]
  have hD : D = C * (P⁻¹ * Q) + Pᴴ⁻¹ := by
    have h1 : D * Pᴴ = C * Qᴴ + 1 := by
      calc D * Pᴴ = C * Qᴴ - (C * Qᴴ - D * Pᴴ) := by abel
        _ = C * Qᴴ + 1 := by rw [s3]; abel
    have h2 := hb
    rw [conjTranspose_mul, conjTranspose_nonsing_inv] at h2
    calc D = D * Pᴴ * Pᴴ⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hPHu, Matrix.mul_one]
      _ = (C * Qᴴ + 1) * Pᴴ⁻¹ := by rw [h1]
      _ = C * (Qᴴ * Pᴴ⁻¹) + Pᴴ⁻¹ := by rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = C * (P⁻¹ * Q) + Pᴴ⁻¹ := by rw [h2]
  have hinner : nbar (C * P⁻¹) * mM P * nU (P⁻¹ * Q) = fromBlocks P Q C D := by
    unfold nbar mM nU
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [fromBlocks_inj]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hPu, Matrix.one_mul]
    · rw [Matrix.mul_assoc, nonsing_inv_mul _ hPu, Matrix.mul_one]
    · rw [hD, Matrix.mul_assoc C, nonsing_inv_mul _ hPu, Matrix.mul_one]
  have hfront : nU ((t : ℂ) • 1) * fromBlocks P Q C D = fromBlocks A B C D := by
    unfold nU
    rw [fromBlocks_multiply]
    simp [hP, hQ]
  refine ⟨mkGR (nU ((t : ℂ) • 1)) (by rw [det_nU]; exact isUnit_one) (inG_nU (by simp)),
    mkGR (nbar (C * P⁻¹)) (by rw [det_nbar]; exact isUnit_one) (inG_nbar hc),
    mkGR (mM P) (isUnit_det_mM hPu) (inG_mM hPu),
    mkGR (nU (P⁻¹ * Q)) (by rw [det_nU]; exact isUnit_one) (inG_nU hb), ?_,
    ⟨t, mR_mkGR _ _ _⟩, ⟨C * P⁻¹, hc, mR_mkGR _ _ _⟩, ⟨P, hPu, mR_mkGR _ _ _⟩,
    ⟨P⁻¹ * Q, hb, mR_mkGR _ _ _⟩⟩
  apply Subtype.ext
  apply Units.ext
  show mR y = mR _ * mR _ * mR _ * mR _
  rw [mR_mkGR, mR_mkGR, mR_mkGR, mR_mkGR, e, ← hfront, ← hinner]
  simp only [Matrix.mul_assoc]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseTau
section
noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open Formalism.IndefR.Eqv (psiT thetaC)

theorem denseTau : DenseTau := by
  intro D n θ τ ι hθ hι y O hO hy
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hcl := DenseP.gam_dense (D := D) DenseP.genSt τ y
  obtain ⟨y', hy'O, γ, hγ, hγe⟩ := mem_closure_iff.1 hcl O hO hy
  have hc : ∀ τ' (w : Formalism.IndefR.Datum.Mx D (n + n) (n + n)), compAt (thetaC D) τ' w = w.map (psiT D τ') :=
    fun _ _ => rfl
  have hy' : (mat (ι y')).map (psiT D τ) = Glob.reidx (mR y') := (hc τ _).symm.trans (hι.2 y').1
  refine ⟨γ, hγ, y', hy'O, γ * (ι y')⁻¹, by group, fun y'' => ?_⟩
  have hR : (mat (γ * (ι y')⁻¹)).map (psiT D τ) = 1 := by
    have h1 : (mat γ).map (psiT D τ) = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (mat (ι y')).map (psiT D τ) := by
      rw [← Matrix.map_mul, ← DenseP.mat_mul, inv_mul_cancel_right]
    rw [hγe, hy'] at h1
    have h2 : Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹) = 1 := by
      rw [← DenseP.reidx_mul]
      show Glob.reidx (mR (y' * y'⁻¹)) = 1
      rw [mul_inv_cancel]; exact DenseP.reidx_one
    calc (mat (γ * (ι y')⁻¹)).map (psiT D τ)
        = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = 1 := by rw [← Matrix.mul_assoc, ← h1, h2]
  generalize γ * (ι y')⁻¹ = x at hR ⊢
  apply Subtype.ext
  apply Units.ext
  show mat (x * ι y'') = mat (ι y'' * x)
  rw [DenseP.mat_mul, DenseP.mat_mul]
  apply Formalism.IndefR.Eqv.mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases h : τ' = τ
    · subst h; rw [hR]; simp only [Matrix.one_mul, Matrix.mul_one]
    · have h1 : (mat (ι y'')).map (psiT D τ') = 1 := by rw [← hc]; exact (hι.2 y'').2.1 τ' h
      rw [h1]; simp only [Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 y'').2.2]; simp only [Matrix.one_mul, Matrix.mul_one]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneSt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DerOneH

variable {D : D7} {n : ℕ}

def hhT (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : GA D V :=
  atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹)

def CurveSt : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (ε : Fin V.rank → Bool) (fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → IsTauFrame V τ s ε fr → IsUe ε X →
    hhT θ V τ fr X 0 = 1 ∧ (∀ a b, hhT θ V τ fr X (a + b) = hhT θ V τ fr X a * hhT θ V τ fr X b) ∧
    ∀ Φ : schwartzA θ V.rank n,
      (∀ y : Mx D V.rank n, Continuous fun p : GA D V × ℝ =>
        Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X p.2)) (HMul.hMul (mt V p.1⁻¹) y))) ∧
      ∀ (z : Mx D V.rank n) (t : ℝ), HasDerivAt (fun u : ℝ => Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X u)) z))
        (DX θ V τ fr X Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X t)) z)) t

end PositivityTheory.Rg.Sw.Glob.DerOneH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def aC (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  Matrix.fromBlocks (Matrix.diagonal fun j => Complex.exp (z * X j)) 0 0 (Matrix.diagonal fun j => Complex.exp (-(z * X j)))

def stripS (X : Fin n → ℝ) : Set ℂ := {z | ∀ j, |z.im * X j| < Real.pi / 4}

def ptZ (y : GR n) (X : Fin n → ℝ) (z : ℂ) (sgnI : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  let M := mR y * aC X z
  (M.toBlocks₁₁ * (sgnI • 1) + M.toBlocks₁₂) * (M.toBlocks₂₁ * (sgnI • 1) + M.toBlocks₂₂)⁻¹

def jC (e : ℤ) (p q : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ) : ℂ :=
  let M := mR y * aC X z
  M.det ^ e * (M.toBlocks₂₁ * (Complex.I • 1) + M.toBlocks₂₂).det ^ (-(p : ℤ)) *
    (M.toBlocks₂₁ * ((-Complex.I) • 1) + M.toBlocks₂₂).det ^ (-(q : ℤ))

def gC {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * c * (Z * gramB (epsT t ε) true u).trace - Complex.I * c * (Z' * gramB (epsT t ε) false u).trace)

def famC {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (y : GR n) (X : Fin n → ℝ) (z : ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  jC e (cnt (epsT t ε) true) (cnt (epsT t ε) false) y X z * gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u

def DReal : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (y : GR n) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    ∀ s : ℝ, famC ε t c e y X s = fun u => jF e (cnt (epsT t ε) true) (cnt (epsT t ε) false) (y * a s) (Complex.I • 1) *
      gZf ε t c (actZ (y * a s) (Complex.I • 1)) u

def DBound : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ y u, DifferentiableOn ℂ (fun z => famC ε t c e y X z u) (stripS X)) ∧
    ContinuousOn (fun p : GR n × ℂ × (Fin m → Fin n → ℂ) => famC ε t c e p.1 X p.2.1 p.2.2) (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) ∧
    ∀ (y₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (δ C : ℝ), N ∈ 𝓝 (y₀, z₀) ∧ 0 < δ ∧
      ∀ p ∈ N, p.2 ∈ stripS X → ∀ u, ‖famC ε t c e p.1 X p.2 u‖ ≤ C * Real.exp (-(δ * ∑ a, ∑ j, ‖u a j‖ ^ 2))

def DCalc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ (s : ℝ) (r : ℕ) (u : Fin m → Fin n → ℂ),
      iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s = (Real.exp (s * (m : ℝ) * ∑ j, X j) : ℂ) *
        fP c ((dil c X ^ r) 1) (fun a j => u a j * Real.exp (s * X j))) ∧
    ∀ (r : ℕ) (s : ℝ), Filter.Tendsto (fun h : ℝ => ∫ u : Fin m → Fin n → ℂ,
        ‖(iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) (s + h) - iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s) / h -
          iteratedDeriv (r + 1) (fun s' : ℝ => famC ε t c e 1 X s' u) s‖ ^ 2) (𝓝[≠] 0) (𝓝 0)

def DifferenceQuotientIsometryExchange : Prop :=
  ∀ (m n : ℕ) (T : ((Fin m → Fin n → ℂ) → ℂ) → ((Fin m → Fin n → ℂ) → ℂ)) (κ : ℝ), 0 < κ →
    (∀ f, IsSch f → IsSch (T f)) → (∀ f g, IsSch f → IsSch g → T (f - g) = T f - T g) →
    (∀ a f, IsSch f → T (fun u => a * f u) = fun u => a * T f u) →
    (∀ f, IsSch f → ∫ u, ‖T f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2) →
    ∀ (G : ℝ → (Fin m → Fin n → ℂ) → ℂ) (G' E' : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ), (∀ s', IsSch (G s')) → IsSch G' →
      Continuous E' → Filter.Tendsto (fun h : ℝ => ∫ u, ‖(G (s + h) u - G s u) / h - G' u‖ ^ 2) (𝓝[≠] 0) (𝓝 0) →
      (∀ u, Filter.Tendsto (fun h : ℝ => (T (G (s + h)) u - T (G s) u) / h) (𝓝[≠] 0) (𝓝 (E' u))) → T G' = E'

def DHol : Prop :=
  GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure →
  ∀ (P : Type) [TopologicalSpace P] [FirstCountableTopology P] (U : Set ℂ), IsOpen U → ∀ φ : P → ℂ → Mx D V.rank n → ℂ,
    (∀ p z, z ∈ U → φ p z ∈ schwartzA θ V.rank n) → (∀ p x, DifferentiableOn ℂ (fun z => φ p z x) U) →
    (∀ x, ContinuousOn (fun pz : P × ℂ => φ pz.1 pz.2 x) (Set.univ ×ˢ U)) →
    (∀ p, ContinuousOn (fun zx : ℂ × Mx D V.rank n => φ p zx.1 zx.2) (U ×ˢ Set.univ)) →
    (∀ (p₀ : P) (z₀ : ℂ), z₀ ∈ U → ∃ (N : Set (P × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧ M ∈ schwartzA θ V.rank n ∧
      ∀ pz ∈ N, pz.2 ∈ U → ∀ x, ‖φ pz.1 pz.2 x‖ ≤ ‖M x‖) →
    let F : P → ℂ → ℂ := fun p z =>
      ⨍ q, descend (GQ V) (fun h => ∑' ξ, φ p z (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν
    ContinuousOn (fun pz : P × ℂ => F pz.1 pz.2) (Set.univ ×ˢ U) ∧ (∀ p, DifferentiableOn ℂ (F p) U) ∧
      ∀ p (r : ℕ) z, z ∈ U → iteratedDeriv r (F p) z =
        ⨍ q, descend (GQ V) (fun h => ∑' ξ, iteratedDeriv r (fun w => φ p w (GlobalTheory.SiegelFormula.invPt V h ξ)) z) q ∂autMeasure V ν

def DSieg : Prop :=
  ∀ (n : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ), z ∈ stripS X →
    IsSiegel (ptZ y X z Complex.I) ∧ IsSiegel (ptZ y X z (-Complex.I))ᴴ ∧
    ((mR y * aC X z).toBlocks₂₁ * (Complex.I • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 ∧
    ((mR y * aC X z).toBlocks₂₁ * ((-Complex.I) • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0

def GCSch : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ), 0 < c → |t| = c → ∀ Z Z' : Matrix (Fin n) (Fin n) ℂ, IsSiegel Z → IsSiegel Z'ᴴ →
    IsSch (gC ε t c Z Z')

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def chN {m : ℕ} (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * t * (b * gramX ε u).trace)

def levF {m : ℕ} (e : ℤ) (a : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  a.det ^ e * (star a.det) ^ ((m : ℤ) - e) * f (Matrix.of u * a)

def vac {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) : (Fin m → Fin n → ℂ) → ℂ := gZf ε t c (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))

def TensInj : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ f g : (Fin V.rank → Fin n → ℂ) → ℂ,
    (∀ Ψ, AwayCls θ τ fr Ψ → tens θ τ fr f Ψ = tens θ τ fr g Ψ) → f = g

def LawN : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → ∀ f, IsSch f →
      L y f = fun u => chN ε (tLoc l τ) b u * f u

def LawM : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∃ e : ℤ, ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f

def LawNbar : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ), cᴴ = c → mR y = nbar c → ∀ f, IsSch f →
      L y f = fun u => ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) *
        ftLoc ε (tLoc l τ) (fun v => chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v) u

def VacK : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L → ∀ e : ℤ,
    (∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f) →
    ∀ k : GR n, InK (mR k) → L k (vac ε (tLoc l τ) (cLoc l τ)) =
      fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) k (Complex.I • 1) *
        vac ε (tLoc l τ) (cLoc l τ) u

def IwaGR : Prop :=
  ∀ (n : ℕ) (y : GR n), ∃ p k : GR n, y = p * k ∧ (mR p).toBlocks₂₁ = 0 ∧ InK (mR k)

def SiegelOrb : Prop :=
  ∀ (n : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z → ∃ q : GR n, (mR q).toBlocks₂₁ = 0 ∧ actZ q (Complex.I • 1) = Z

def CocycleZ : Prop :=
  ∀ (n : ℕ) (e : ℤ) (p q : ℕ) (y y' : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
    IsUnit ((mR y').toBlocks₂₁ * Z + (mR y').toBlocks₂₂).det ∧ IsUnit ((mR y').toBlocks₂₁ * Zᴴ + (mR y').toBlocks₂₂).det ∧
    IsSiegel (actZ y' Z) ∧ actZ (y * y') Z = actZ y (actZ y' Z) ∧ jF e p q (y * y') Z = jF e p q y (actZ y' Z) * jF e p q y' Z

def LocMul : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ (y y' : GR n) f, IsSch f → L (y * y') f = L y (L y' f)

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenSt
section
noncomputable section

open scoped Matrix

namespace PositivityTheory.Rg.Sw.Glob

def SchOps : Prop :=
  ∀ (m n : ℕ), (∀ f g : (Fin m → Fin n → ℂ) → ℂ, IsSch f → IsSch g → IsSch (fun u => f u + g u)) ∧
    (∀ (c : ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsSch f → IsSch (fun u => c * f u)) ∧
    (∀ (a : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsUnit a.det → IsSch f →
      IsSch (fun u => f (Matrix.of u * a))) ∧
    (∀ (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), bᴴ = b → IsSch f →
      IsSch (fun u => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace) * f u)) ∧
    ∃ f : (Fin m → Fin n → ℂ) → ℂ, IsSch f ∧ f 0 = 1

end PositivityTheory.Rg.Sw.Glob
end
end

