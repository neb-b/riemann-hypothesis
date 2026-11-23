module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cj (D : D7) : AE D →+* AE D := sigR (AF D.host.F) D.sp.cm.sig

def cjU (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (cj D).toMonoidHom

def trA (D : D7) : AE D →ₗ[AF D.host.F] AF D.host.F := Algebra.trace (AF D.host.F) (AE D)

def half (D : D7) : AF D.host.F := algebraMap D.host.F (AF D.host.F) (1 / 2)

abbrev WA (A B : HSp D) : Type := Matrix (Fin A.rank) (Fin B.rank) (AE D)

def colMat {A B : HSp D} (x : WA A B) : Matrix (Fin B.rank) (Fin A.rank) (AE D) := xᵀ

def ofLin (A B : HSp D) (x : A.V →ₗ[D.host.E] B.V) : WA A B :=
  ((LinearMap.toMatrix A.frame B.frame x).map (incA D))ᵀ

def WQ (A B : HSp D) : AddSubgroup (WA A B) :=
  (AddMonoidHom.mapMatrix (incA D).toAddMonoidHom :
    Matrix (Fin A.rank) (Fin B.rank) D.host.E →+ WA A B).range

def gramA (V : HSp D) : Matrix (Fin V.rank) (Fin V.rank) (AE D) := V.gram.map (incA D)

def gramInvA (V : HSp D) : Matrix (Fin V.rank) (Fin V.rank) (AE D) := (V.gram⁻¹).map (incA D)

def adj {A B : HSp D} (x : WA A B) : WA B A :=
  (HMul.hMul (HMul.hMul (gramInvA A) (Formalism.UG.cT (cj D) (colMat x))) (gramA B))ᵀ

def herm {A B : HSp D} (x x' : WA A B) : AE D := Matrix.trace (HMul.hMul (colMat (adj x')) (colMat x))

def symp {A B : HSp D} (x x' : WA A B) : AF D.host.F := trA D (incA D D.host.xi0 * herm x x')

def riem {A B : HSp D} (x x' : WA A B) : AF D.host.F := -symp x x'

theorem herm_add_left {A B : HSp D} (x y z : WA A B) : herm (x + y) z = herm x z + herm y z := by
  simp [herm, colMat, Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]

theorem symp_add_left {A B : HSp D} (x y z : WA A B) : symp (x + y) z = symp x z + symp y z := by
  simp only [symp, herm_add_left, mul_add, map_add (f := _)]

theorem symp_zero_left {A B : HSp D} (x : WA A B) : symp 0 x = 0 := by
  have := symp_add_left (0 : WA A B) 0 x
  rw [add_zero] at this
  exact left_eq_add.mp this

def gMat {V : HSp D} (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) (AE D) := (matHom V g).1

def act {A B : HSp D} (p : GA D A × GA D B) (x : WA A B) : WA A B :=
  (HMul.hMul (HMul.hMul (gMat p.2) (colMat x)) (gMat p.1⁻¹))ᵀ

def detA (V : HSp D) : GA D V →* (AE D)ˣ := Matrix.GeneralLinearGroup.det.comp (matHom V)

def trInf (D : D7) (x : Ainf D.host.F) : ℝ :=
  ∑ v : InfinitePlace D.host.F, (v.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding v (x v)).re

def IsStdChar (D : D7) (s : ℤˣ) (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  IsCharAF D.host.F ψ ∧
    ∀ x : Ainf D.host.F, psiInf D.host.F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((s : ℤ) : ℂ) * (trInf D x : ℂ))

def hsymp {A B : HSp D} (x x' : WA A B) : AF D.host.F := half D * symp x x'

def rho {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (u : WA A B) : Module.End ℂ (WA A B → ℂ) where
  toFun := fun (f : WA A B → ℂ) (w : WA A B) => (ψ (hsymp w u) : ℂ) * f (w + u)
  map_add' f g := funext fun w => mul_add (ψ (hsymp w u) : ℂ) (f (w + u)) (g (w + u))
  map_smul' c f := funext fun w => mul_left_comm (ψ (hsymp w u) : ℂ) c (f (w + u))

def thetaFun (A B : HSp D) : (WA A B → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 0

def realAd (D : D7) (s : InfinitePlace D.host.F → ℝ) : AF D.host.F :=
  pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (fun v => s v.1, 0)) 0

def realPt (D : D7) (p : (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)) : AE D :=
  realAd D p.1 ⊗ₜ[D.host.F] (1 : D.host.E) + realAd D p.2 ⊗ₜ[D.host.F] D.host.xi0

structure IsTheta {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (f : WA A B → ℂ) : Prop where
  law : ∀ γ ∈ WQ A B, ∀ w, f (γ + w) = (ψ (hsymp w γ) : ℂ) * f w
  smooth : ∀ w : WA A B, ContDiff ℝ ∞
    fun p : Fin A.rank → Fin B.rank → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ) =>
      f (w + Matrix.of fun i j => realPt D (p i j))
  level : ∃ U : AddSubgroup (WA A B), IsOpen (U : Set (WA A B)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → rho ψ u f = f

def Theta (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) : Submodule ℂ (WA A B → ℂ) where
  carrier := {f | IsTheta ψ f}
  zero_mem' := ⟨fun _ _ _ => by simp, fun _ => contDiff_const, ⊤, isOpen_univ, fun _ _ _ => map_zero _⟩
  add_mem' := by
    rintro f g ⟨f1, f2, U, hU, f3⟩ ⟨g1, g2, U', hU', g3⟩
    refine ⟨fun γ hγ w => ?_, fun w => (f2 w).add (g2 w), U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
    · simp only [Pi.add_apply, f1 γ hγ w, g1 γ hγ w, mul_add]
    · rw [map_add (f := _), f3 u hu.1 h0, g3 u hu.2 h0]
  smul_mem' := by
    rintro c f ⟨f1, f2, U, hU, f3⟩
    refine ⟨fun γ hγ w => ?_, fun w => (f2 w).const_smul c, U, hU, fun u hu h0 => ?_⟩
    · simp only [Pi.smul_apply, f1 γ hγ w, smul_eq_mul, mul_left_comm]
    · rw [map_smul, f3 u hu h0]

@[reducible] def measWA (A B : HSp D) : MeasurableSpace (WA A B) := borel _

def IsProbPair (A B : HSp D) (μ : @Measure (WA A B) (measWA A B)) (𝓕 : Set (WA A B)) : Prop :=
  letI := measWA A B
  μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (WQ A B) 𝓕 μ ∧ μ 𝓕 = 1

def IsNormSq {A B : HSp D} (f : WA A B → ℂ) (N : ENNReal) : Prop :=
  AllSome (fun m : @Measure (WA A B) (measWA A B) × Set (WA A B) => IsProbPair A B m.1 m.2) fun m =>
    letI := measWA A B
    ∫⁻ w in m.2, ‖f w‖ₑ ^ 2 ∂m.1 = N

def Implements {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (M : Module.End ℂ (Theta ψ A B))
    (p : GA D A × GA D B) : Prop :=
  ∀ (w : WA A B) (f f' : Theta ψ A B), (f' : WA A B → ℂ) = rho ψ w f →
    ((M f' : Theta ψ A B) : WA A B → ℂ) = rho ψ (act p w) (M f : Theta ψ A B)

def idemFin (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))


open Classical in
def idemInf (D : D7) (v : InfinitePlace D.host.F) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F (Pi.single v 1) 0)

structure IsSplitIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) : Prop where
  idem : IsIdempotentElem e
  orth : e * cj D e = 0
  sum : e + cj D e = idemFin D v

def wComp (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (e z : AE D) : Fv D.host.F v :=
  evalV D.host.F v (sndA D.host.F (trA D (e * z)))

def absV (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fv D.host.F v) : ℝ :=
  (WithZeroMulInt.toNNReal (e := (Ideal.absNorm v.asIdeal : NNReal))
    (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)) (Valued.v y) : NNReal)

def IsAt {V : HSp D} (e : AE D) (g : GA D V) : Prop := (1 - e) • gMat g = (1 - e) • (1 : Matrix _ _ (AE D))

def atIdem {R : Type} [CommRing R] {e : R} (he : IsIdempotentElem e) : Rˣ →* Rˣ where
  toFun u := ⟨e * u + (1 - e), e * ↑u⁻¹ + (1 - e),
    by have h1 := u.mul_inv; have h2 := he.eq
       linear_combination (e * e) * h1 + (2 - (u : R) - ↑u⁻¹) * h2,
    by have h1 := u.mul_inv; have h2 := he.eq
       linear_combination (e * e) * h1 + (2 - (u : R) - ↑u⁻¹) * h2⟩
  map_one' := by ext; simp
  map_mul' u u' := by
    ext
    have h2 := he.eq
    simp only [Units.val_mul]
    linear_combination (-((u : R) * u') + u + u' - 1) * h2

def lagr (A B : HSp D) (e : AE D) : Set (WA A B) := {x | e • x = x}

def splitChar (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) {e : AE D} (he : IsIdempotentElem e) :
    GA D A × GA D B →* Circle :=
  ((χB.comp ((atIdem he).comp (detA A))).comp (MonoidHom.fst _ _))⁻¹ *
    (χA.comp ((atIdem he).comp (detA B))).comp (MonoidHom.snd _ _)

def splitMod (A B : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (p : GA D A × GA D B) : ℝ :=
  absV D v (wComp D v e (detA A p.1 : (AE D)ˣ)) ^ ((B.rank : ℝ) / 2) *
    absV D v (wComp D v e (detA B p.2 : (AE D)ˣ)) ^ (-(A.rank : ℝ) / 2)

def splitScalar (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}
    (he : IsSplitIdem D v e) (p : GA D A × GA D B) : ℂ :=
  ((splitChar A B χA χB he.idem p : Circle) : ℂ) * (splitMod A B v e p : ℂ)

def ActsBy {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (e : AE D) (M : Module.End ℂ (Theta ψ A B)) (c : ℂ) : Prop :=
  ∀ l : Theta ψ A B →ₗ[ℂ] ℂ,
    (∀ y ∈ lagr A B (cj D e), ∀ f f' : Theta ψ A B, (f' : WA A B → ℂ) = rho ψ y f → l f' = l f) →
    ∀ f, l (M f) = c * l f

structure IsWeil {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (Theta ψ A B)) : Prop where
  impl : ∀ p, Implements (om p) p
  unitary : ∀ p (f : Theta ψ A B), ∃ N, N ≠ ⊤ ∧ IsNormSq (f : WA A B → ℂ) N ∧
    IsNormSq ((om p f : Theta ψ A B) : WA A B → ℂ) N
  cont : ∀ (f : Theta ψ A B) (w : WA A B), Continuous fun p => ((om p f : Theta ψ A B) : WA A B → ℂ) w
  rat : ∀ g ∈ GQ A, ∀ h ∈ GQ B, ∀ f : Theta ψ A B,
    thetaFun A B ((om (g, h) f : Theta ψ A B) : WA A B → ℂ) = thetaFun A B (f : WA A B → ℂ)
  split : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (he : IsSplitIdem D v e) (p : GA D A × GA D B),
    IsAt (idemFin D v) p.1 → IsAt (idemFin D v) p.2 → ActsBy e (om p) (splitScalar A B χA χB he p)

end GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance 100] LieRing.ofAssociativeRing

def lieU {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [conjTranspose_add, add_mul, mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hX, smul_zero]
  lie_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    have h1 : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
    rw [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
      mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2, mul_sub]
    simp only [neg_mul, neg_neg, mul_assoc]
    abel

variable {D : D7}

abbrev LieAt (V : HSp D) (τ : D.what₂.Tau) : Type := lieU (gramAt D V τ)

abbrev LieInf (V : HSp D) : Type := ∀ τ : D.what₂.Tau, LieAt V τ


open Classical in
def atPlace (V : HSp D) (τ : D.what₂.Tau) (X : LieAt V τ) : LieInf V := Pi.single τ X

def IsExpFam (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (e : LieInf V → GA D V) : Prop :=
  ∀ X, e X ∈ GinfC V ∧
    ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (e X) = NormedSpace.exp (X τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def IsSmoothInf (V : HSp D) (e : LieInf V → GA D V) (φ : GA D V → ℂ) : Prop :=
  ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : (∀ τ : D.what₂.Tau, (lieU (gramAt D V τ)).toSubmodule) => φ (g * e fun τ => ⟨(X τ).1, (X τ).2⟩))

end Smooth

def lieDer (V : HSp D) (e : LieInf V → GA D V) (X : LieInf V) (φ : GA D V → ℂ) : GA D V → ℂ :=
  fun g => deriv (fun t : ℝ => φ (g * e (t • X))) 0

def wordDer (V : HSp D) (e : LieInf V → GA D V) (l : List (LieInf V)) (φ : GA D V → ℂ) : GA D V → ℂ :=
  l.foldr (lieDer V e) φ

abbrev EnvAt (V : HSp D) (τ : D.what₂.Tau) : Type := UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LieAt V τ)

def envOf (V : HSp D) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) : EnvAt V τ :=
  w.sum fun l c => c • (l.map fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)).prod

def envDer (V : HSp D) (e : LieInf V → GA D V) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) (φ : GA D V → ℂ) :
    GA D V → ℂ :=
  w.sum fun l c => c • wordDer V e (l.map (atPlace V τ)) φ

def IsZFiniteAt (V : HSp D) (e : LieInf V → GA D V) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {ψ : GA D V → ℂ |
    ∃ w : List (LieAt V τ) →₀ ℂ, envOf V τ w ∈ Subalgebra.center ℂ (EnvAt V τ) ∧ ψ = envDer V e τ w φ})

def finCoord (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F :=
  (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y

def finNorm (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) : NNReal :=
  Finset.univ.sup fun p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
    ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g p.1 p.2.1) p.2.2)‖₊

def finHt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) : NNReal :=
  max 1 (max (finNorm V v g) (finNorm V v g⁻¹))

def infNorm (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) :
    NNReal :=
  ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g)‖₊

def infHt (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) :
    NNReal :=
  max 1 (max (infNorm θ V τ g) (infNorm θ V τ g⁻¹))

theorem eventually_finNorm_le_one (V : HSp D) (g : GA D V) : ∀ᶠ v in Filter.cofinite, finNorm V v g ≤ 1 := by
  have h : ∀ p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E), ∀ᶠ v in Filter.cofinite,
      ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g p.1 p.2.1) p.2.2)‖₊ ≤ 1 := by
    intro p
    refine (finCoord D (finMat D.sp.cm.sig V.gram g p.1 p.2.1) p.2.2).2.mono fun v hv => ?_
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 hv
  refine (Filter.eventually_all.2 h).mono fun v hv => ?_
  exact Finset.sup_le fun p _ => hv p

theorem finHt_mulSupport_finite (V : HSp D) (g : GA D V) : (Function.mulSupport fun v => finHt V v g).Finite := by
  have h := (eventually_finNorm_le_one V g).and (eventually_finNorm_le_one V g⁻¹)
  refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
  exact max_eq_left (max_le hv'.1 hv'.2)

def height (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) : NNReal :=
  (∏ τ, infHt θ V τ g) * ∏ᶠ v, finHt V v g

theorem one_le_height (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) :
    1 ≤ height θ V g :=
  one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun _ _ => le_max_left _ _)
    (one_le_finprod' fun _ => le_max_left _ _)

def IsUnifModerate (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (e : LieInf V → GA D V)
    (φ : GA D V → ℂ) : Prop :=
  ∃ N : ℕ, ∀ l : List (LieInf V), ∃ C : ℝ, ∀ g, ‖wordDer V e l φ g‖ ≤ C * (height θ V g : ℝ) ^ N

def IsSmoothAutForm (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  IsAutFun V φ ∧
    AllSome (IsInfFam (D := D)) fun θ => AllSome (IsExpFam θ V) fun e =>
      IsSmoothInf V e φ ∧ (∀ τ, IsZFiniteAt V e τ φ) ∧ IsUnifModerate θ V e φ

end GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

end
end

