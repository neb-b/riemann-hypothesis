module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

def re (x : A ℚ) : ℝ := TR.pInf ℚ x Rat.infinitePlace

def iy (y : ℝ) : (A ℚ)ˣ :=
  if h : y = 0 then 1 else TR.infId ℚ ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩

def rot (t : ℝ) : GL (Fin 2) (A ℚ) :=
  TR.infGL ℚ 2 (Matrix.SpecialLinearGroup.toGL ⟨!![fun _ => Real.cos t, fun _ => -Real.sin t; fun _ => Real.sin t, fun _ => Real.cos t], by
    rw [Matrix.det_fin_two_of]
    funext w
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.one_apply]
    nlinarith [Real.sin_sq_add_cos_sq t]⟩)

def ThR (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) (g : GL (Fin 2) (A ℚ)) : ℂ :=
  ∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* g.val) j

def Bad (N : ℕ) (v : H.P ℚ) : Prop := (N : 𝓞 ℚ) ∈ v.asIdeal

def Dv (N : ℕ) (v : H.P ℚ) (x : A ℚ) : Prop := Valued.v (H.cp v x) ≤ Valued.v (N : H.Kv v)

def Lev (N : ℕ) (k : GL (Fin 2) (A ℚ)) : Prop :=
  (∀ i j, (k.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1) ∧
    ∀ v, H.KAt v k ∧ ∀ i j, Dv N v (k.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)

def ChOk (χ : HChar ℚ) (N : ℕ) : Prop := ∀ t ∈ UU, (∀ v, Dv N v ((t : A ℚ) - 1)) → χ.1 t = 1

def PhiN (N : ℕ) (p : MvPolynomial (Fin 2) ℂ) (x : Fin 2 → A ℚ) : ℂ :=
  if ∀ v, Dv N v (x 0) ∧ Dv N v (x 1 - 1) then
    MvPolynomial.eval (fun i => (re (x i) : ℂ)) p * Complex.exp (-(Real.pi : ℂ) * ((re (x 0) ^ 2 + re (x 1) ^ 2 : ℝ) : ℂ)) else 0

variable {E : Type} [Field E] [NumberField E]

def Wo (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) : ℂ :=
  ∫ u in FS2 ℚ, φ (nE D u * h) * ψ (u 1) ∂(adeleMeasurePi ℚ)

def Ir (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) : ℂ :=
  ∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) ∂M.μ ∂U.υ

def Zs (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (2 * s * t) * Ir M U χ φ Φ t

def Zu (D : Dat ℚ E) (M : Meas ℚ) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ) : ℂ :=
  ∫ k, ∫ y : IdeleGroup ℚ, Wo D φ (em E (aE y * gl k)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) *
    ∫ z : IdeleGroup ℚ, (Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)
      ∂(ideleMeasure ℚ) ∂(ideleMeasure ℚ) ∂M.κ

def Mk (D : Dat ℚ E) (χ : HChar ℚ) (k : ℕ) (φ : GL (Fin 2) (A E) → ℂ) (p : MvPolynomial (Fin 2) ℂ) (s : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p *
    ∫ y : ℝ, Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)

structure admitted (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) : Prop where
  cont : Continuous φ
  left : ∀ γ g, φ (ratGL E 2 γ * g) = φ g
  cen : ∀ z g, φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 (ideleNorm ℚ E z) : ℂˣ) : ℂ) * φ g
  zero : ∀ h, ∫ u in FS2 ℚ, φ (nE D u * h) ∂(adeleMeasurePi ℚ) = 0
  bdd : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B
  decay : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∀ c : ℝ, 0 < c → ∀ r : ℕ,
    ∃ B : ℝ, ∀ b a, ∀ k ∈ C, c ≤ ab a → ‖φ (gl (nU b * mD a) * k)‖ ≤ B * (ab a)⁻¹ ^ r
  wdec : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧ ∀ r : ℕ, ∃ B : ℝ,
    ∀ y : (A ℚ)ˣ, ∀ k ∈ C, ‖Wo D φ (em E (aE y) * k)‖ ≤ B * ((1 + |re y|) ^ r)⁻¹ ∧ (Wo D φ (em E (aE y) * k) ≠ 0 → (y : A ℚ).2 ∈ K)

variable [_root_.NumberField.IsTotallyComplex E]

structure Gd (D : Dat ℚ E) (P : CuspSub E 2) (L N : ℕ) (φ : GL (Fin 2) (A E) → ℂ) : Prop where
  pos : 0 < N
  dvd : L ∣ N
  same : ∀ v, Bad N v → Bad L v
  mem : φ ∈ Tr P
  pl : ∀ v, ¬ Bad N v → H.Gd D.δ v
  fix : ∀ w : H.P E, ¬ Bad N (w.under (𝓞 ℚ)) → H.Fix w φ ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B φ
  lev : ∀ k, Lev N k → ∀ g, φ (g * em E k) = φ g
  supp : ∀ (y : (A ℚ)ˣ) x, Wo D φ (em E (aE y) * infGL E 2 x) ≠ 0 → ∀ v, Bad N v → Dv L v ((y : A ℚ) - 1)
  tor : ∀ t ∈ UU, (∀ v, Dv L v ((t : A ℚ) - 1)) → ∀ (y : (A ℚ)ˣ) x,
    Wo D φ (em E (aE (y * t)) * infGL E 2 x) = Wo D φ (em E (aE y) * infGL E 2 x)

structure IsAs (P : CuspSub E 2) (χ : HChar ℚ) (N : ℕ) (a : ℕ → ℂ) : Prop where
  one : a 1 = 1
  mul : ∀ m n, m.Coprime n → a (m * n) = a m * a n
  bad : ∀ p k : ℕ, p.Prime → p ∣ N → a (p ^ (k + 1)) = 0
  split : ∀ v, ¬ Bad N v → ∀ w w' : H.P E, w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → ∀ α β α' β' : ℂˣ,
    (CG.mk P).HasSat w {α, β} → (CG.mk P).HasSat w' {α', β'} →
    (PowerSeries.mk fun k => a (normV v ^ k)) * ((1 - PowerSeries.C ((α * α' * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) *
      (1 - PowerSeries.C ((α * β' * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) * (1 - PowerSeries.C ((β * α' * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) *
      (1 - PowerSeries.C ((β * β' * χ.val v : ℂˣ) : ℂ) * PowerSeries.X)) = 1
  inert : ∀ v, ¬ Bad N v → ∀ w : H.P E, w.under (𝓞 ℚ) = v → normV w = normV v ^ 2 → ∀ α β : ℂˣ, (CG.mk P).HasSat w {α, β} →
    (PowerSeries.mk fun k => a (normV v ^ k)) * ((1 - PowerSeries.C ((α * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) *
      (1 - PowerSeries.C ((β * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) * (1 - PowerSeries.X ^ 2)) = 1

def Unit1 (ω : HChar ℚ) : Prop := ∀ a, ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1

def Entire (a : ℕ → ℂ) : Prop := ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 4 < s.re → F s = LSeries a s

def AllA (p : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], Dat ℚ E → CuspSub E 2 → HChar ℚ → HChar ℚ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
    CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → p E D P ω χ

def TrAdm : Prop := AllA fun _ _ _ _ D P ω _ => ∀ φ ∈ Tr P, admitted D ω φ

def PerTr : Prop := AllA fun _ _ _ _ D P ω χ => (∀ φ ∈ Tr P, admitted D ω φ) → ∀ M U, NoPer M U χ P → ∀ φ ∈ Tr P, Per M U χ φ = 0

def Ent : Prop := AllA fun _ _ _ _ D _ ω χ => ∀ M U φ, admitted D ω φ → Per M U χ φ = 0 → ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2),
  Differentiable ℂ (Zs M U χ φ Φ)

def Unf : Prop := AllA fun _ _ _ _ D _ ω χ => ∀ M U, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ, admitted D ω φ → ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2),
  ∀ s : ℂ, 4 < s.re → Zs M U χ φ Φ s = c * Zu D M χ φ Φ s

def PhiMem : Prop := ∀ N p, 0 < N → PhiN N p ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)

def Fac : Prop := AllA fun _ _ _ _ D P ω χ => ∀ M L N, ChOk χ L → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a →
  ∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) → ∀ s : ℂ, 4 < s.re → LSeriesSummable a s →
    Zu D M χ φ (PhiN N p) s = c * ((Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e)) * LSeries a s * Mk D χ 0 φ p s

def Shift : Prop := AllA fun E _ _ _ D P _ _ => ∀ L N φ, Gd D P L N φ → ∃ φ₀ φ₁ φ₂, Gd D P L N φ₀ ∧ Gd D P L N φ₁ ∧ Gd D P L N φ₂ ∧ ∀ y t : ℝ, y ≠ 0 →
  (y : ℂ) * Wo D φ (em E (aE (iy y) * rot t)) = (Real.sin t : ℂ) ^ 2 * Wo D φ₀ (em E (aE (iy y) * rot t)) +
    (Real.sin t : ℂ) * (Real.cos t : ℂ) * Wo D φ₁ (em E (aE (iy y) * rot t)) + (Real.cos t : ℂ) ^ 2 * Wo D φ₂ (em E (aE (iy y) * rot t))

def ShiftM : Prop := AllA fun _ _ _ _ D P _ χ => ∀ L N k φ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), Gd D P L N φ → p.IsHomogeneous (2 * e) →
  ∃ (n : ℕ) (f : Fin n → _) (q : Fin n → MvPolynomial (Fin 2) ℂ), (∀ i, Gd D P L N (f i) ∧ (q i).IsHomogeneous (2 * (e + k))) ∧
    ∀ s : ℂ, 4 < s.re → Mk D χ k φ p s = ∑ i, Mk D χ 0 (f i) (q i) s

def Hol : Prop := AllA fun _ _ _ _ D _ ω χ => ∀ k φ p, admitted D ω φ → DifferentiableOn ℂ (Mk D χ k φ p) {s | 1 - (k : ℝ) < s.re}

def NonZ : Prop := AllA fun _ _ _ _ D P ω χ => (∀ φ ∈ Tr P, admitted D ω φ) → ∀ L N φ, Gd D P L N φ → Wo D φ 1 ≠ 0 → ∀ (k : ℕ) (s : ℂ), 1 - (k : ℝ) < s.re →
  ∃ (φ' : _) (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), Gd D P L N φ' ∧ p.IsHomogeneous (2 * e) ∧ Mk D χ k φ' p s ≠ 0

def ExGd : Prop := AllA fun _ _ _ _ D P ω _ => (∀ φ ∈ Tr P, admitted D ω φ) → ∀ N₀, 0 < N₀ → ∃ L N φ, N₀ ∣ L ∧ Gd D P L N φ ∧ Wo D φ 1 ≠ 0

def ChEx : Prop := ∀ χ : HChar ℚ, ∃ N₀, 0 < N₀ ∧ ∀ N, N₀ ∣ N → ChOk χ N

def SatU : Prop := AllA fun E _ _ _ _ P _ _ => ∀ (w : H.P E) (α β : ℂˣ), (CG.mk P).HasSat w {α, β} →
  ‖(α * β : ℂ)‖ = 1 ∧ starRingEnd ℂ (α + β : ℂ) * (α * β) = α + β ∧ ‖(α : ℂ)‖ ^ 2 ≤ normV w

def AsEx : Prop := AllA fun _ _ _ _ D P _ χ => ∀ L N φ, Gd D P L N φ → ∃ a, IsAs P χ N a ∧ ∀ s : ℂ, 4 < s.re → LSeriesSummable a s

def Ext : Prop := AllA fun _ _ _ _ D P _ χ => ∀ M U, NoPer M U χ P → ∀ L N φ, ChOk χ L → Gd D P L N φ → Wo D φ 1 ≠ 0 →
  ∀ a, IsAs P χ N a → (∀ s : ℂ, 4 < s.re → LSeriesSummable a s) → Entire a

def Landau : Prop := ∀ b : ℕ → ℂ, (∀ n, 0 ≤ b n) → b 1 = 1 → (∀ s : ℂ, 4 < s.re → LSeriesSummable b s) → Entire b →
  {n | 1 ≤ b n}.Finite

def Lan : Prop := AllA fun E _ _ _ D P ω χ => ∀ η : HChar ℚ, χ = ω⁻¹ → ∀ L N φ, Gd D P L N φ →
  (∀ w : H.P E, ¬ Bad N (w.under (𝓞 ℚ)) → η.val (w.under (𝓞 ℚ)) = if normV w = normV (w.under (𝓞 ℚ)) then 1 else -1) →
  (∀ w w' : H.P E, ¬ Bad N (w.under (𝓞 ℚ)) → w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) → ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat w' B) →
  ChOk ω⁻¹ L → ChOk (ω * η)⁻¹ L → ∀ a a', IsAs P ω⁻¹ N a → IsAs P (ω * η)⁻¹ N a' → (∀ s : ℂ, 4 < s.re → LSeriesSummable a s) →
  (∀ s : ℂ, 4 < s.re → LSeriesSummable a' s) → Entire a → Entire a' → False

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section Objects

variable {E : Type} [Field E] [NumberField E]

def UI (β : (A E)ˣ → ℂ) : ℂ := ∫ z in normOneFundamentalDomain E, β (z : IdeleGroup E) ∂normOneMeasure E

def sZ (D : Dat ℚ E) (z : (A E)ˣ) : GL (Fin 2) (A E) := aE z * dM (Units.map (D.bar : A E →* A E) z)⁻¹

def SLP (M : Meas ℚ) (φ : GL (Fin 2) (A E) → ℂ) : ℂ := ∫ g in M.D, φ (em E (gl g)) ∂M.μ

def UPer (D : Dat ℚ E) (M : Meas ℚ) (φ : GL (Fin 2) (A E) → ℂ) : ℂ := UI fun z => SLP M fun x => φ (x * sZ D z)

variable (E) in
structure MeasE where
  μ : Measure (G1 E)
  D : Set (G1 E)
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  meas : MeasurableSet D
  fund : IsFundamentalDomain (Gam E) D μ

def mean (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ) : ℂ := ∫ h in N.D, Ψ (gl h) ∂N.μ

def J1 (D : Dat ℚ E) (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ) : ℂ := UI fun z => mean N fun x => Ψ (x * sZ D z)

def II (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ) : ℂ := UI fun t => mean N fun x => Ψ (x * aE t)

abbrev rp (ξ : Fin 4 → ℚ) : V4 ℚ := fun i => rt (ξ i)

def qr (δ : ℚ) (ξ : Fin 4 → ℚ) : ℚ := ξ 2 ^ 2 - δ * ξ 3 ^ 2 - ξ 1 * ξ 0

def ThOn (S : Set (Fin 4 → ℚ)) (φ : V4 ℚ → ℂ) : ℂ := ∑' ξ : S, φ (rp ξ.1)

def X0 : Fin 4 → ℚ := ![0, 0, 0, 1]

def PosInv (π : TR.CuspSub ℚ 2) : Prop :=
  ∀ f ∈ π.V, ∀ s g, f.1 (GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s * g) = f.1 g

variable [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D) (N : MeasE E)

def fOn (S : Set (Fin 4 → ℚ)) (ph : S4 ℚ) (φ : GL (Fin 2) (A E) → ℂ) (g : G1 ℚ) : ℂ :=
  J1 D N fun x => ThOn S (W.Om g (W.L x ph)).1 * φ x

def f0 (ph : S4 ℚ) (φ : GL (Fin 2) (A E) → ℂ) (g : G1 ℚ) : ℂ := J1 D N fun x => Th (W.Om g (W.L x ph)).1 * φ x

end Objects

def All (Q : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E), Weil D → Meas ℚ → MeasE E → CuspSub E 2 → Prop) :
    Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (W : Weil D) (M : Meas ℚ) (N : MeasE E) (P : CuspSub E 2),
    Q E D W M N P

def MeasEEx : Prop := ∀ (E : Type) [Field E] [NumberField E], Nonempty (MeasE E)

def VolE : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E), N.μ N.D < ⊤

def RedE : Prop := ∀ (E : Type) [Field E] [NumberField E], ∃ (c : ℝ) (C : Set (G1 E)), 0 < c ∧ IsCompact C ∧
  ∀ h : G1 E, ∃ γ u b, ∃ k ∈ C, ratS E γ * h = nU u * mD b * k ∧ c ≤ ab b

def InvE : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E),
  (∀ t, MeasurePreserving (cD t) N.μ N.μ) ∧ ∀ Ψ : GL (Fin 2) (A E) → ℂ, LRat Ψ →
    (∀ h : G1 E, (mean N fun x => Ψ (x * gl h)) = mean N Ψ) ∧ ∀ γ, (mean N fun x => Ψ (x * ratGL E 2 γ)) = mean N Ψ

def TorCo : Prop := ∀ (E : Type) [Field E] [NumberField E], ∃ α : G1 E → IdeleGroup E, Measurable α ∧
  (∀ u h, α (nU u * h) = α h) ∧ ∀ t h, α (mD t * h) = t * α h

def SzLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E),
  (∀ z z', sZ D (z * z') = sZ D z * sZ D z') ∧ Continuous (sZ D) ∧ (∀ z, nu ℚ (sZ D z) = 1) ∧ (∀ h : G1 E, nu ℚ (gl h) = 1) ∧
  (∀ z, D.act (sZ D z) (rp X0) = rp X0) ∧ (∀ g : G1 ℚ, D.act (em E (gl g)) (rp X0) = rp X0) ∧
  (∀ e : Eˣ, ∃ γ, sZ D (IdeleGroup.diagonal E e) = ratGL E 2 γ) ∧
  (∀ z g, sZ D z * em E (gl g) = em E (gl (cD (ideleNorm ℚ E z)⁻¹ g)) * sZ D z) ∧
  (∀ z, sZ D z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * em E (dM (ideleNorm ℚ E z)⁻¹)) ∧
  (∀ x, nu ℚ x = 1 → ∀ v, q4 D.δ (D.act x v) = q4 D.δ v) ∧ ∀ ξ, q4 D.δ (rp ξ) = rt (qr D.δ ξ)

def LatSum : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ))
  (C : Set (GL (Fin 2) (A E))) (c : ℝ) (s : ℕ), IsCompact K → IsCompact C → (∀ k ∈ C, nu ℚ k = 1) → 0 < c →
    ∃ (n r : ℕ) (B : ℝ), ∀ (a : (A ℚ)ˣ) u (b : (A E)ˣ), ∀ k ∈ C, c ≤ ab a → c ≤ ab b →
      (Summable fun ξ : Fin 4 → ℚ => wt K n fun i => (a : A ℚ) * D.act (gl (nU u * mD b) * k)⁻¹ (rp ξ) i) ∧
      ∑' ξ : Fin 4 → ℚ, (wt K n fun i => (a : A ℚ) * D.act (gl (nU u * mD b) * k)⁻¹ (rp ξ) i) ≤ B * ab b ^ r ∧
      ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, (wt K n fun i => (a : A ℚ) * D.act (gl (nU u * mD b) * k)⁻¹ (rp ξ.1) i) ≤
        B * (ab a)⁻¹ ^ s * ab b ^ r

def DecE : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2), ∀ φ ∈ P.V,
  Pp.Lf φ.1 ∧ (∀ g, ∫ b in fundamentalSet E, φ.1 (gl (nU b) * g) ∂(adeleMeasure E) = 0) ∧
  ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∀ c : ℝ, 0 < c → ∀ r : ℕ,
    ∃ B : ℝ, ∀ b a, ∀ k ∈ C, c ≤ ab a → ‖φ.1 (gl (nU b * mD a) * k)‖ ≤ B * (ab a)⁻¹ ^ r

def Maj : Prop := All fun E _ _ _ D W _ _ P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, ∀ C : Set (GL (Fin 2) (A E)), IsCompact C →
  (∀ k ∈ C, nu ℚ k = 1) → ∀ c : ℝ, 0 < c → ∀ s : ℕ, ∃ B : ℝ, ∀ b a, ∀ k' ∈ KK ℚ, c ≤ ab a → ∀ h : G1 E, ∀ k ∈ C,
    (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖) ∧
    (∑' ξ : Fin 4 → ℚ, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * k)‖ ≤ B * ab a ^ 2 ∧
    (∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ.1)‖) * ‖φ.1 (gl h * k)‖ ≤
      B * (ab a)⁻¹ ^ s

def ThCont : Prop := All fun E _ _ _ D W _ _ _ => ∀ ph ∈ Fock D.δ, ∀ S : Set (Fin 4 → ℚ),
  ContinuousOn (fun p : G1 ℚ × GL (Fin 2) (A E) => ThOn S (W.Om p.1 (W.L p.2 ph)).1) {p | nu ℚ p.2 = 1}

def MeanZero : Prop := All fun _ _ _ _ _ _ _ N P => ∀ φ ∈ P.V, ∀ y, (mean N fun x => φ.1 (x * y)) = 0

def Orb1 : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E),
  (∀ γ : SpecialLinearGroup (Fin 2) E, ∃ ρ : (Fin 4 → ℚ) ≃ₗ[ℚ] (Fin 4 → ℚ), ∀ ξ, D.act (gl (ratS E γ)) (rp ξ) = rp (ρ ξ)) ∧
  (∀ ξ, ξ ≠ 0 → qr D.δ ξ = 0 → ∃ (γ : SpecialLinearGroup (Fin 2) E) (r : ℚ), r ≠ 0 ∧ rp ξ = D.act (gl (ratS E γ)) (rp ![0, r, 0, 0])) ∧
  (∀ (γ : SpecialLinearGroup (Fin 2) E) (r r' : ℚ), r ≠ 0 → D.act (gl (ratS E γ)) (rp ![0, r, 0, 0]) = rp ![0, r', 0, 0] → γ 1 0 = 0) ∧
  (∀ γ : SpecialLinearGroup (Fin 2) E, γ 1 0 = 0 → ∃ c : ℚ, c ≠ 0 ∧ ∀ r, D.act (gl (ratS E γ)) (rp ![0, r, 0, 0]) = rp ![0, c * r, 0, 0]) ∧
  ∀ (u : A E) (r : ℚ), D.act (gl (nU u)) (rp ![0, r, 0, 0]) = rp ![0, r, 0, 0]

def OrbS : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E),
  (∀ ξ, qr D.δ ξ = qr D.δ X0 → ∃ γ : SpecialLinearGroup (Fin 2) E, rp ξ = D.act (gl (ratS E γ)) (rp X0)) ∧
  (∀ h : G1 E, D.act (gl h) (rp X0) = rp X0 ↔ ∃ g : G1 ℚ, gl h = em E (gl g)) ∧
  ∀ γ : SpecialLinearGroup (Fin 2) E, D.act (gl (ratS E γ)) (rp X0) = rp X0 ↔ ∃ g, gl (ratS E γ) = em E (gl (ratS ℚ g))

def Rank1 : Prop := All fun _ _ _ _ D W _ N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, ∀ g y, nu ℚ y = 1 →
  (mean N fun x => ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y)) = 0

def ThetaLiftEqAnisotropicPart : Prop := All fun _ _ _ _ D W _ N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, f0 W N ph φ.1 = fOn W N {ξ | qr D.δ ξ ≠ 0} ph φ.1

def Coef : Prop := All fun _ _ _ _ D W _ N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, ∀ (t : ℚ) g,
  ∫ b in fundamentalSet ℚ, fOn W N {ξ | qr D.δ ξ ≠ 0} ph φ.1 (nU b * g) * ψ (-(b * rt t)) ∂(adeleMeasure ℚ) =
    ((adeleMeasure ℚ).real (fundamentalSet ℚ) : ℝ) * fOn W N {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = t} ph φ.1 g

structure CuspFn (u : G1 ℚ → ℂ) : Prop where
  cont : Continuous u
  left : LInv u
  bdd : ∃ B : ℝ, ∀ g, ‖u g‖ ≤ B
  cusp : ∀ g, ∫ b in fundamentalSet ℚ, u (nU b * g) ∂(adeleMeasure ℚ) = 0

def ThetaLiftIsBoundedCuspidal : Prop := All fun _ _ _ _ D W _ N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, CuspFn (f0 W N ph φ.1)

def Dens : Prop := ∀ (M : Meas ℚ) (u : G1 ℚ → ℂ), CuspFn u → u ≠ 0 →
  ∃ π : TR.CuspSub ℚ 2, PosInv π ∧ ∃ f ∈ π.V, ∫ g in M.D, f.1 (gl g) * u g ∂M.μ ≠ 0

def Fub : Prop := All fun _ _ _ _ D W M N P => ∀ ph ∈ Fock D.δ, ∀ φ ∈ P.V, ∀ π : TR.CuspSub ℚ 2, ∀ f ∈ π.V,
  ∫ g in M.D, f.1 (gl g) * f0 W N ph φ.1 g ∂M.μ = J1 D N fun x => lift W M f.1 ph x * φ.1 x

def MomKill : Prop := ∀ (δ : ℚ), δ < 0 → ∀ (Y : Type) [MeasurableSpace Y] (m : Measure Y) [SFinite m] (p : Y → V4 ℚ) (w : Y → ℂ),
  Measurable p → Measurable w → (∀ K, IsCompact K → ∃ n, Integrable (fun y => (wt K n (p y) : ℂ) * w y) m) →
  (∀ ph ∈ Fock δ, ∫ y, ph.1 (p y) * w y ∂m = 0) →
  ∀ Ψ : V4 ℚ → ℂ, Measurable Ψ → Integrable (fun y => Ψ (p y) * w y) m → ∫ y, Ψ (p y) * w y ∂m = 0

def OrbFn : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (M : Meas ℚ) (j : G1 ℚ →* G1 E),
  (∀ g, gl (j g) = em E (gl g)) → ∀ c : G1 E → ℂ, Continuous c → HasCompactSupport c →
    ∃ Ψ : V4 ℚ → ℂ, Measurable Ψ ∧ ∀ h : G1 E, Ψ (D.act (gl h)⁻¹ (rp X0)) = ∫ g, c (j g * h) ∂M.μ

def CoefPer : Prop := All fun E _ _ _ D W M N P => ∀ φ ∈ P.V,
  (∀ ph ∈ Fock D.δ, fOn W N {ξ | qr D.δ ξ = qr D.δ X0} ph φ.1 1 = 0) → ∀ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) = 0

def PerU : Prop := All fun E _ _ _ D W M _ P => ∀ (U : UMeas) (ω : HChar ℚ), GlobalTheory.DiscSpec.IsNormalised P → CenN P ω →
  (∀ φ ∈ P.V, ∀ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) = 0) → NoPer M U ω⁻¹ P ∧ NoPer M U (ω * W.η)⁻¹ P

def Rev : Prop := All fun E _ _ _ D W M N P => (∃ φ ∈ P.V, ∃ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) ≠ 0) →
  ∃ π : TR.CuspSub ℚ 2, PosInv π ∧ ∃ f ∈ π.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (J1 D N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0

def ToII : Prop := All fun _ _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  (∃ f ∈ π.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (J1 D N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0) →
  ∃ π' : TR.CuspSub ℚ 2, PosInv π' ∧ ∃ f ∈ π'.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (II N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0

end UpperTheory.ConvolutionTheory.RankTwoDescent
end
end

