module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0002
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvolutionRealPlacePairs
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

section HostLemmas

variable {R : Ranks} (H : Host R)

theorem sigmaOf_mul (g h : R.GG) : H.sigmaOf (g * h) = H.sigmaOf g * H.sigmaOf h := by
  unfold Host.sigmaOf
  exact map_mul _ g h

theorem sigmaOf_one : H.sigmaOf 1 = 1 := by
  unfold Host.sigmaOf
  exact map_one _

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g := by
  unfold Host.sigmaOf
  exact MulEquiv.apply_symm_apply _ _

theorem sigmaOf_sqrt_neg (g : R.GG) (h : g.1.2 = -1) : H.sigmaOf g H.sqrtMinusD = -H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sigmaOf_sqrt_pos (g : R.GG) (h : g.1.2 = 1) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sqrt_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem emb_sigmaOf (g h : R.GG) (x : H.E) : H.emb g (H.sigmaOf h x) = H.emb (g * h) x := by
  unfold Host.emb
  rw [sigmaOf_mul]
  rfl

end HostLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Polynomial
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section KurLemmas

variable {p : ℕ} [Fact p.Prime]

theorem mem_Kur_of_pow {x : ℂ_[p]} (n : ℕ) (hn : 0 < n) (hd : ¬ p ∣ n) (hx : x ^ n = 1) : x ∈ MaximalUnramifiedExtension p :=
  Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, hn, hd, hx⟩)

variable {R : Ranks} (H : Host R) (J : H.E →+* ℂ_[p])

end KurLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section Fixed

variable {R : Ranks} (H : Host R)

def sInv (R : Ranks) : R.GG := ((1, -1), 1)

end Fixed

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.MainNotions.G (plGG)

theorem embT_tauPl (D : D7) (z : Bool × HH D) : TaylorLogMetric.embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold TaylorLogMetric.embT tauPl
  rw [Equiv.apply_symm_apply]

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : (D.eTau (tauPl D z) : D.R.GG) = plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem tauSg_tauPl (D : D7) (b : Bool) (t : HH D) : TaylorLogMetric.tauSg D (tauPl D (b, t)) = tauPl D (!b, t) := by
  have hm : plGG D (b, t) * TaylorLogMetric.sgm D = plGG D (!b, t) := by
    cases b <;> refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, TaylorLogMetric.sgm]
  have hmem : (D.eTau (tauPl D (b, t)) : D.R.GG) * TaylorLogMetric.sgm D ∈ D.R.Psi := by
    rw [eTau_tauPl, hm]; exact plGG_mem_Psi D _
  rw [show TaylorLogMetric.tauSg D (tauPl D (b, t)) = D.eTau.symm ⟨_, hmem⟩ from dif_pos hmem]
  refine (Equiv.symm_apply_eq _).2 (Subtype.ext ?_)
  simp only [eTau_tauPl, hm]

theorem inertia_pairs : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p],
    ∃ (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) ∧ δ ^ 2 = -(p : D.host.E) ∧
    cE δ = -δ ∧ s δ = -δ ∧ (∀ y, s (s y) = y) ∧ (∀ y, s (cE y) = cE (s y)) ∧
    Function.Injective (fun z : Bool × HH D => TaylorLogMetric.embT D (tauPl D z)) ∧
    (∀ τ ρ, TaylorLogMetric.embT D τ δ = TaylorLogMetric.embT D ρ δ) ∧
    (∀ (t : HH D) y, TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) ∧
    (∀ τ y, s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) ∧ Function.Bijective (tauPl D) ∧
    ∀ t : HH D, TaylorLogMetric.tauSg D (tauPl D (false, t)) = tauPl D (true, t) ∧
      TaylorLogMetric.tauSg D (tauPl D (true, t)) = tauPl D (false, t) := by
  intro D p _ hp ι
  have hp2 : p ≠ 2 := by rw [hp]; exact D.host.hypOdd.2.2.2.2
  have hpq : D.host.q ≠ p := by rw [hp]; exact D.host.hypOdd.2.2.1
  refine ⟨D.host.conj.toRingEquiv, (D.host.sigmaOf (sInv D.R)).toRingEquiv, D.host.sqrtMinusD, fun y => rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, tauPl_bij D, fun t => ⟨tauSg_tauPl D false t, tauSg_tauPl D true t⟩⟩
  · rw [sqrt_sq, hp]
  · exact sigmaOf_sqrt_neg D.host (D.R.cc) rfl
  · exact sigmaOf_sqrt_neg D.host (sInv D.R) rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (sInv D.R) y) = y
    rw [← AlgEquiv.mul_apply, ← sigmaOf_mul]
    have : sInv D.R * sInv D.R = 1 := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [sInv]
    rw [this, sigmaOf_one]
    rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y) = D.host.sigmaOf (D.R.cc) (D.host.sigmaOf (sInv D.R) y)
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← sigmaOf_mul, ← sigmaOf_mul, mul_comm]
  · intro z z' h
    have h' : ∀ x, D.host.φ₀ (D.host.sigmaOf (plGG D z) x) = D.host.φ₀ (D.host.sigmaOf (plGG D z') x) := fun x => by
      have := RingHom.congr_fun h x
      simp only [embT_tauPl] at this
      exact this
    have hs : D.host.sigmaOf (plGG D z) = D.host.sigmaOf (plGG D z') :=
      AlgEquiv.ext fun x => D.host.φ₀.injective (h' x)
    have hg : plGG D z = plGG D z' := by
      unfold Host.sigmaOf at hs
      exact (D.host.gal).symm.injective hs
    apply (tauPl_bij D).1
    unfold tauPl
    congr 1
    exact Subtype.ext hg
  · intro τ ρ
    change D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) D.host.sqrtMinusD) =
      D.host.φ₀ (D.host.sigmaOf (D.eTau ρ : D.R.GG) D.host.sqrtMinusD)
    rw [sigmaOf_sqrt_pos D.host _ (D.eTau τ).2, sigmaOf_sqrt_pos D.host _ (D.eTau ρ).2]
  · intro t y
    change D.host.emb _ y = D.host.emb _ (D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y))
    rw [eTau_tauPl, eTau_tauPl, emb_sigmaOf, emb_sigmaOf]
    have hg : plGG D (false, t) * sInv D.R * D.R.cc = plGG D (true, t) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, sInv, Formalism.HC.Frame.cc, c0]
    rw [hg]
  · intro τ y hy
    have hy' : D.host.sigmaOf (sInv D.R) y = y := hy
    exact UpperTheory.Ram.image_mem_of_fixed_iod D.host ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D τ)) (MaximalUnramifiedExtension p)
      (fun z hz => mem_Kur_of_pow _ (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos)
        (by rw [hp]; exact D.host.toHostRaw.d_not_dvd_QSq) hz) y hy'

end GlobalTheory.InertiaPairs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

section Pure

variable (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K]

def IsInt (x : K) : Prop := ∃ o : O, algebraMap O K o = x

def IntM {m n : ℕ} (x : Matrix (Fin m) (Fin n) K) : Prop := ∀ i j, IsInt O (x i j)

def GInt {n : ℕ} (x : GL (Fin n) K) : Prop := IntM O x.1 ∧ IntM O (x⁻¹).1

def Hk (p : O) (j : ℕ) {n : ℕ} (x : GL (Fin n) K) : Prop :=
  IntM O x.1 ∧ IntM O (algebraMap O K p • (x⁻¹).1) ∧ ∃ u : Oˣ, x.1.det = algebraMap O K (p ^ j * u)

def Reps {n : ℕ} {ι : Type} (x : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) : Prop :=
  (∀ γ ∈ R, ∃ k₁ k₂, GInt O k₁ ∧ GInt O k₂ ∧ ρ γ = k₁ * x * k₂) ∧
    ∀ k₁ k₂, GInt O k₁ → GInt O k₂ → ∃! γ, γ ∈ R ∧ GInt O ((ρ γ)⁻¹ * (k₁ * x * k₂))

variable {O}

theorem isInt_iff {x : K} : IsInt O x ↔ x ∈ (algebraMap O K).range := Iff.rfl

theorem intM_iff {m n : ℕ} {x : Matrix (Fin m) (Fin n) K} :
    IntM O x ↔ ∃ A : Matrix (Fin m) (Fin n) O, A.map (algebraMap O K) = x := by
  constructor
  · intro h
    choose A hA using h
    exact ⟨Matrix.of A, by ext i j; simp [hA]⟩
  · rintro ⟨A, rfl⟩ i j
    exact ⟨A i j, rfl⟩

theorem IntM.mul {l m n : ℕ} {x : Matrix (Fin l) (Fin m) K} {y : Matrix (Fin m) (Fin n) K} (hx : IntM O x)
    (hy : IntM O y) : IntM O (x * y) := by
  rw [intM_iff] at hx hy ⊢
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  exact ⟨A * B, Matrix.map_mul⟩

theorem IntM.add {m n : ℕ} {x y : Matrix (Fin m) (Fin n) K} (hx : IntM O x) (hy : IntM O y) : IntM O (x + y) := fun i j => by
  obtain ⟨a, ha⟩ := hx i j
  obtain ⟨b, hb⟩ := hy i j
  exact ⟨a + b, by simp [ha, hb]⟩

theorem IntM.sub {m n : ℕ} {x y : Matrix (Fin m) (Fin n) K} (hx : IntM O x) (hy : IntM O y) : IntM O (x - y) := fun i j => by
  obtain ⟨a, ha⟩ := hx i j
  obtain ⟨b, hb⟩ := hy i j
  exact ⟨a - b, by simp [ha, hb]⟩

theorem IntM.transpose {m n : ℕ} {x : Matrix (Fin m) (Fin n) K} (hx : IntM O x) : IntM O xᵀ := fun i j => hx j i

theorem intM_one {n : ℕ} : IntM O (1 : Matrix (Fin n) (Fin n) K) := fun i j => by
  by_cases h : i = j
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Matrix.one_apply_ne h]⟩

theorem gInt_one {n : ℕ} : GInt O (1 : GL (Fin n) K) := ⟨intM_one, by rw [inv_one]; exact intM_one⟩

theorem GInt.mul {n : ℕ} {x y : GL (Fin n) K} (hx : GInt O x) (hy : GInt O y) : GInt O (x * y) := ⟨IntM.mul hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact IntM.mul hy.2 hx.2⟩

theorem GInt.inv {n : ℕ} {x : GL (Fin n) K} (hx : GInt O x) : GInt O x⁻¹ := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

end Pure

variable {D : D7}

abbrev Ov (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := v.adicCompletionIntegers D.host.F

theorem isInt_Ov {v : HeightOneSpectrum (𝓞 D.host.F)} {x : Fv D.host.F v} :
    IsInt (Ov D v) x ↔ x ∈ v.adicCompletionIntegers D.host.F := ⟨fun ⟨o, h⟩ => h ▸ o.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

def Chart (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v) : Prop :=
  Function.Surjective π ∧ (∀ a, π a = 0 ↔ e * a = 0) ∧
    (∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y)) ∧
    ∀ a, finPart D (e * a) ∈ intAE D ↔ IsInt (Ov D v) (π a)

def Frame (V : HSp D) (e : AE D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) : Prop :=
  ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ LamHat V ↔
    ∀ i, IsInt (Ov D v) (((β⁻¹).1 *ᵥ fun k => π (y k)) i)

def rho (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) : GA D V →* GL (Fin V.rank) (Fv D.host.F v) :=
  (MulAut.conj β⁻¹).toMonoidHom.comp ((Matrix.GeneralLinearGroup.map π).comp (matHom V))

theorem rho_val (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (rho V π β g).1 = (β⁻¹).1 * (mt V g).map π * β.1 := by
  simp only [rho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul]
  rfl

end GlobalTheory.SplitHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLine
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLine

theorem isUnit_of_stable_line : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l),
  (∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB) → GlobalTheory.RegularRing.LineUnit (P.PD K) →
  ∀ b : Bst P, b ≠ 0 → (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b := by
  intro l _ P _ K hno hLU b hb hst
  unfold GlobalTheory.RegularRing.LineUnit at hLU
  haveI : CharZero P.R.B := charZero_of_injective_algebraMap (algebraMap ℚ_[l] P.R.B).injective

  have hact : ∀ (g : GQ l) (p : Bst P),
      actSt P g p = stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB)) p := fun g p => rfl

  have hder : ∀ (g : GQ l) (p : Bst P), derivative (actSt P g p) = actSt P g (derivative p) := by
    intro g p
    rw [hact, hact, derivative_stHom]
    simp
  have hiter : ∀ (k : ℕ) (g : GQ l) (p : Bst P),
      actSt P g (derivative^[k] p) = derivative^[k] (actSt P g p) := by
    intro k g
    induction k with
    | zero => intro p; rfl
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hder]

  have heig : ∀ (k : ℕ) (g : ↥(GK K)), ∃ x : ℚ_[l],
      actSt P (g : GQ l) (derivative^[k] b) = algebraMap ℚ_[l] (Bst P) x * derivative^[k] b := by
    intro k g
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [hiter, hx, Polynomial.algebraMap_apply, iterate_derivative_C_mul]

  have hlin : ∀ p : Bst P, p.natDegree ≤ 1 → p.coeff 1 ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) p = algebraMap ℚ_[l] (Bst P) x * p) → False := by
    intro p hp1 hp0 hpe
    obtain ⟨u, v, rfl⟩ : ∃ u v, p = C u * X + C v := ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one hp1⟩
    have hu0 : u ≠ 0 := by simpa using hp0
    have hco : ∀ (g : GQ l), g ∈ GK K → ∃ x : ℚ_[l],
        P.actQ g u = algebraMap ℚ_[l] P.R.B x * u ∧
        P.actQ g u * ((kummer P g : ℚ_[l]) • P.tB) + P.actQ g v = algebraMap ℚ_[l] P.R.B x * v := by
      intro g hg
      obtain ⟨x, hx⟩ := hpe ⟨g, hg⟩
      refine ⟨x, ?_, ?_⟩
      · have h1 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 1) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h1
      · have h0 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 0) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h0
    have hU : IsUnit u := hLU u hu0 (fun g => by
      obtain ⟨x, h1, -⟩ := hco (g : GQ l) g.2
      exact ⟨x, by rw [P.PD_actB]; exact h1⟩)
    obtain ⟨w, hw⟩ : ∃ w, w = v * ↑hU.unit⁻¹ := ⟨_, rfl⟩
    have hwu : w * u = v := by rw [hw, mul_assoc, IsUnit.val_inv_mul, mul_one]
    refine hno (-w) (fun g hg => ?_)
    obtain ⟨x, h1, h0⟩ := hco g hg
    have hne : P.actQ g u ≠ 0 := (hU.map (P.actQ g)).ne_zero
    have key : P.actQ g w * P.actQ g u = (w - (kummer P g : ℚ_[l]) • P.tB) * P.actQ g u := by
      rw [← map_mul, hwu]
      linear_combination h0 - w * h1 - (algebraMap ℚ_[l] P.R.B x) * hwu
    have hgw : P.actQ g w = w - (kummer P g : ℚ_[l]) • P.tB := mul_right_cancel₀ hne key
    rw [map_neg, hgw]
    ring
  by_cases hn : b.natDegree = 0
  · obtain ⟨c, rfl⟩ : ∃ c, b = C c := ⟨_, eq_C_of_natDegree_eq_zero hn⟩
    apply IsUnit.map C
    refine hLU c (fun h => hb (by rw [h, C_0])) (fun g => ?_)
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [P.PD_actB]
    rw [actSt_C, Polynomial.algebraMap_apply, ← C_mul] at hx
    exact C_injective hx
  · exfalso
    apply hlin (derivative^[b.natDegree - 1] b)
    · have := natDegree_iterate_derivative b (b.natDegree - 1)
      omega
    · rw [coeff_iterate_derivative, show 1 + (b.natDegree - 1) = b.natDegree by omega]
      refine smul_ne_zero ?_ (leadingCoeff_ne_zero.mpr hb)
      intro h
      rw [Nat.descFactorial_eq_zero_iff_lt] at h
      omega
    · exact heig (b.natDegree - 1)

end GlobalTheory.Pst.StLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTransportIsometry
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.ThLoc.LocPull

open Formalism.L2.Th1.H (blk4 pow4 slice imgLat tens4 kernel4)

variable {n : Type} [Fintype n] [DecidableEq n]

def diagonalPowFourEquiv (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun z w := φ (slice w.1 z) w.2
  invFun z w := φ.symm (slice w.1 z) w.2
  map_add' x y := by
    funext w
    have e : slice w.1 (x + y) = slice w.1 x + slice w.1 y := rfl
    simp only [e, map_add (f := _), Pi.add_apply]
  map_smul' c x := by
    funext w
    have e : slice w.1 (c • x) = c • slice w.1 x := rfl
    simp only [e, map_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ (slice w'.1 z) w'.2) = φ (slice w.1 z) := rfl
    simp only [e, LinearEquiv.symm_apply_apply]
    rfl
  right_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ.symm (slice w'.1 z) w'.2) = φ.symm (slice w.1 z) := rfl
    simp only [e, LinearEquiv.apply_symm_apply]
    rfl

theorem slice_pow4E (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (a : Fin 4) (z : Fin 4 × n → ℂ) :
    slice a (diagonalPowFourEquiv φ z) = φ (slice a z) := rfl

theorem fourCopiesHermitianForm_eq_sum_blocks (h : Matrix n n ℂ) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) x y = ∑ a : Fin 4, matH h (slice a x) (slice a y) := by
  show (∑ w, ∑ w', x w * blk4 h w w' * conj (y w')) = ∑ a : Fin 4, ∑ i, ∑ j, x (a, i) * h i j * conj (y (a, j))
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [blk4]
  · intro b _ hb
    simp [blk4, Ne.symm hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem blockwiseActionOnFourCopies_isometry (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (h : Matrix n n ℂ)
    (hφ : IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ))) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y) = matH (blk4 h) x y := by
  rw [fourCopiesHermitianForm_eq_sum_blocks, fourCopiesHermitianForm_eq_sum_blocks]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [slice_pow4E, slice_pow4E]
  exact hφ _ _

theorem imgLat_pull (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    imgLat (((diagonalPowFourEquiv φ).trans g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
        (pow4 (Λ.comap φ.toLinearMap.toAddMonoidHom)) =
      imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨diagonalPowFourEquiv φ x, fun a => hx a, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(diagonalPowFourEquiv φ).symm x, fun a => ?_, ?_⟩
    · show φ (slice a ((diagonalPowFourEquiv φ).symm x)) ∈ Λ
      rw [← slice_pow4E, LinearEquiv.apply_symm_apply]
      exact hx a
    · show g (diagonalPowFourEquiv φ ((diagonalPowFourEquiv φ).symm x)) = g x
      rw [LinearEquiv.apply_symm_apply]

theorem locNorm_pull : ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)), IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h (Λ.comap φ.toLinearMap.toAddMonoidHom) (fun z => θ (φ z)) p ι := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι φ hφ H
  obtain ⟨g₁, ε, hiso, hnd, hidx, hε, hker⟩ := H
  have hI := imgLat_pull φ Λ g₁
  refine ⟨(diagonalPowFourEquiv φ).trans g₁, ε, ?_, ?_, ?_, hε, ?_⟩
  · intro x y
    exact (hiso (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y)).trans (blockwiseActionOnFourCopies_isometry φ h hφ x y)
  · rw [hI]
    exact hnd
  · rw [hI]
    exact hidx
  · funext z
    have t1 : tens4 (fun z => θ (φ z)) z = tens4 θ (diagonalPowFourEquiv φ z) := rfl
    rw [t1, hker]
    simp only [Pi.smul_apply]
    congr 1
    unfold kernel4
    rw [hI]
    rfl

end GlobalTheory.ThLoc.LocPull
end
end

