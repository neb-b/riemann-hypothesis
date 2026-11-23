module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormula
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem trace_diagonal_block_conjugate (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hg : IsUnit g.det)
    (hX : X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)))
    (hb : ∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g))
      = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal (fun i => ((d i : ℝ) : ℂ)) with hD
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) with hB
  have h1 : g * D * g⁻¹ = X := by
    rw [← hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.mul_one]
  have h2 : trace (D * (g⁻¹ * B * g)) = trace (X * B) := by
    rw [← h1]
    have : D * (g⁻¹ * B * g) = (D * g⁻¹ * B) * g := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h2]
  have h3 : trace (X * B) = ∑ u, ∑ w, X (e u) (e w) *
      (Matrix.fromBlocks Y 0 0 0 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ) w u := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [hB, Matrix.reindex_apply]
  rw [h3]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, hb]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]

end GlobalTheory.CompanionTheory.RgHeFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingBasisEval
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobFac

theorem T_fac : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {B : Type} [Field B] (ι : C₀ →+* B) (i : A →+* B), (∀ a, ι (c a) = i a) → ∀ (h : L →+ B), (∀ (w : W) y, h (w • y) = i (algebraMap W A w) * h y) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)), ∃ E : K₀ ⊗[W] L →+ B, (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) ∧ ∀ G : A ⊗[W] L →+ B, (∀ a y, G (a ⊗ₜ y) = i a * h y) → ∀ z, G z = ∑ s, ι (T c k hk (b.coord s) z) * E (b s) := by
  intro W A C₀ _ _ _ _ K₀ _ _ L _ _ c k hk B _ ι i hi h hh m b
  let E : K₀ ⊗[W] L →+ B := TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun y => ι (k x) * h y
          map_zero' := by simp
          map_add' := fun y y' => by simp [mul_add] }
      map_zero' := by
        ext y
        simp
      map_add' := fun x x' => by
        ext y
        simp [add_mul] }
    (fun r x y => by
      show ι (k (r • x)) * h y = ι (k x) * h (r • y)
      rw [hh, Algebra.smul_def, map_mul, hk, map_mul, hi]
      ring)
  have hE : ∀ x y, E (x ⊗ₜ y) = ι (k x) * h y := by
    intro x y
    first
    | rfl
    | simp [E, TensorProduct.liftAddHom_tmul]
  have hEs : ∀ (x : K₀) (t : K₀ ⊗[W] L), E (x • t) = ι (k x) * E t := by
    intro x t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y =>
      rw [TensorProduct.smul_tmul', hE, hE, smul_eq_mul, map_mul, map_mul, mul_assoc]
    | add t t' ht ht' =>
      rw [smul_add, map_add (f := _), map_add (f := _), ht, ht', mul_add]
  refine ⟨E, hE, fun G hG z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    have hsum : ∑ s, ι (T c k hk (b.coord s) (a ⊗ₜ y)) * E (b s) =
        ι (c a) * E ((1 : K₀) ⊗ₜ y) := by
      conv_rhs => rw [← b.sum_repr ((1 : K₀) ⊗ₜ y)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      have hT : T c k hk (b.coord s) (a ⊗ₜ y) = c a * k (b.repr ((1 : K₀) ⊗ₜ y) s) := by
        first
        | rfl
        | simp [T, TensorProduct.liftAddHom_tmul, Module.Basis.coord_apply]
      rw [hEs, hT, map_mul, mul_assoc]
    rw [hG, hsum, hE, map_one, map_one, one_mul, hi]
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy, add_mul, Finset.sum_add_distrib]

end GlobalTheory.CompanionTheory.FrobFac
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingFrobeniusCompat
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_phi_expand {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    {F : W →+* W} (φA : A →+* A) (φC : C₀ →+* C₀) (φL : L →ₛₗ[F] L) (fr : K₀ →+* K₀)
    (φD : K₀ ⊗[W] L →+ K₀ ⊗[W] L) (hD : ∀ x y, φD (x ⊗ₜ y) = fr x ⊗ₜ φL y)
    (pT : A ⊗[W] L →+ A ⊗[W] L) (hT : ∀ a y, pT (a ⊗ₜ y) = φA a ⊗ₜ φL y)
    (hφ : ∀ a, φC (c a) = c (φA a)) (hφk : ∀ x, φC (k x) = k (fr x))
    {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) (f : Module.Dual K₀ (K₀ ⊗[W] L))
    (z : A ⊗[W] L) :
    T c k hk f (pT z) = ∑ s, φC (T c k hk (b.coord s) z) * k (f (φD (b s))) := by
  have hsmul : ∀ (x : K₀) (v : K₀ ⊗[W] L), φD (x • v) = fr x • φD v := by
    intro x v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y =>
      rw [TensorProduct.smul_tmul', hD, hD, smul_eq_mul, map_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add v₁ v₂ h₁ h₂ => rw [smul_add, map_add (f := _), map_add (f := _), h₁, h₂, smul_add]
  have hTt : ∀ (g : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (y : L),
      T c k hk g (a ⊗ₜ y) = c a * k (g (1 ⊗ₜ y)) := fun g a y => rfl
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [hT, hTt]
    simp_rw [hTt, map_mul, hφ, hφk]
    have h1 : (1 : K₀) ⊗ₜ[W] φL y = φD (1 ⊗ₜ y) := by rw [hD, map_one]
    have h2 : φD ((1 : K₀) ⊗ₜ[W] y) = ∑ s, fr (b.coord s (1 ⊗ₜ y)) • φD (b s) := by
      conv_lhs => rw [← b.sum_repr ((1 : K₀) ⊗ₜ[W] y)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [hsmul]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, h2, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul, map_mul]
    ring
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add (f := _), map_add (f := _), h₁, h₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_add (f := _), map_add (f := _), add_mul]

end GlobalTheory.CompanionTheory.FrobPairing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingGaloisEquivariant
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_gal {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀]
    [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀)
    (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) (σA : A →+* A) (σC : C₀ →+* C₀)
    (gT : A ⊗[W] L →+ A ⊗[W] L) (hg : ∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y)
    (hσ : ∀ a, σC (c a) = c (σA a)) (hσk : ∀ x, σC (k x) = k x)
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) :
    T c k hk f (gT z) = σC (T c k hk f z) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a y
    rw [hg]
    simp only [T, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, hσ, hσk]
  · intro x y hx hy
    simp only [map_add (f := _), hx, hy]

end GlobalTheory.CompanionTheory.FrobPairing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingLTensorNaturality
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPsi

theorem T_lTensor {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀)
    (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L)
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L') :
    T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a y =>
    rw [LinearMap.lTensor_tmul, T_tmul, T_tmul, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  | add z z' hz hz' => simp only [map_add (f := _), hz, hz']

end GlobalTheory.CompanionTheory.FrobPsi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulDual
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPsi

theorem T_ksmul : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk (x • f) z = k x * T c k hk f z := by
  intro W A C₀ _ _ _ _ K₀ _ _ L _ _ c k hk x f z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [T_tmul, T_tmul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz', mul_add]

end GlobalTheory.CompanionTheory.FrobPsi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulLeft
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPairing

theorem T_smul {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
    {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
    (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))
    (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L) :
    T c k hk f (a • z) = c a * T c k hk f z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul b y =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp only [T, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, mul_assoc]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]

end GlobalTheory.CompanionTheory.FrobPairing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupCoordApply
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

variable {W : Type} [Fintype W] {n M : ℕ}

abbrev TupV (W : Type) [Fintype W] (n M : ℕ) : Type :=
  PiLp 2 (fun _ : W × Fin M => EuclideanSpace ℂ (Fin n))

def tupCoord : TupV W n M ≃L[ℝ] (W → Fin n → Fin M → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x w a p => x (w, p) a
      invFun := fun X => WithLp.toLp 2 fun k => WithLp.toLp 2 fun a => X k.1 a k.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem tupCoord_apply (x : TupV W n M) (w : W) (a : Fin n) (p : Fin M) :
    tupCoord x w a p = x (w, p) a := rfl

def diagOp (b : W → Matrix (Fin n) (Fin n) ℂ) : TupV W n M →ₗ[ℂ] TupV W n M where
  toFun y := WithLp.toLp 2 fun k => Matrix.toEuclideanLin (b k.1).transpose (y k)
  map_add' x y := by
    ext k : 2
    simp
  map_smul' c x := by
    ext k : 2
    simp

@[simp] theorem diagOp_apply (b : W → Matrix (Fin n) (Fin n) ℂ) (y : TupV W n M) (k : W × Fin M) :
    diagOp b y k = Matrix.toEuclideanLin (b k.1).transpose (y k) := rfl

def mixOp (J : W → Matrix (Fin M) (Fin M) ℂ) : TupV W n M →ₗ[ℂ] TupV W n M where
  toFun z := WithLp.toLp 2 fun k => (2 : ℂ) • ∑ j, J k.1 k.2 j • z (k.1, j)
  map_add' x y := by
    ext k : 2
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext k : 2
    simp [Finset.smul_sum, smul_smul, mul_comm, mul_left_comm]
    exact Finset.sum_congr rfl fun _ _ => by ring

@[simp] theorem mixOp_apply (J : W → Matrix (Fin M) (Fin M) ℂ) (z : TupV W n M) (k : W × Fin M) :
    mixOp J z k = (2 : ℂ) • ∑ j, J k.1 k.2 j • z (k.1, j) := rfl

def polarOp (J : W → Matrix (Fin M) (Fin M) ℂ) (b : W → Matrix (Fin n) (Fin n) ℂ) :
    TupV W n M →ₗ[ℝ] TupV W n M :=
  ((mixOp J).comp (diagOp b)).restrictScalars ℝ

theorem polarOp_apply (J : W → Matrix (Fin M) (Fin M) ℂ) (b : W → Matrix (Fin n) (Fin n) ℂ)
    (y : TupV W n M) : polarOp J b y = mixOp J (diagOp b y) := rfl

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerEqMapOfSurjective
section
open GlobalTheory.PRep

namespace GlobalTheory.CompanionTheory.PRep

theorem twKer_eq_map_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (N : Subgroup G) (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W) (hf : Function.Surjective f)
    (hint : ∀ g v, f (ρ g v) = σ g (f v)) : twKer σ N θ = (twKer ρ N θ).map f := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨n, w', rfl⟩
    obtain ⟨v, rfl⟩ := hf w'
    exact ⟨ρ n v - (θ n : ℂ) • v, ⟨n, v, rfl⟩, by rw [map_sub, map_smul, hint]⟩
  · rintro ⟨_, ⟨n, v, rfl⟩, rfl⟩
    exact ⟨n, f v, by rw [map_sub, map_smul, hint]⟩

theorem twKer_map_closed : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G)
    (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W), Function.Surjective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    twKer σ N θ = (twKer ρ N θ).map f :=
  fun ρ σ N θ f hf hint => GlobalTheory.CompanionTheory.PRep.twKer_eq_map_of_surjective ρ σ N θ f hf hint

end GlobalTheory.CompanionTheory.PRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationPowerIff
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PowComp

theorem smodEq_span_iff {S : Type} [CommRing S] (a x y : S) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule S S)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem val_pow_iff {S : Type} [CommRing S] (ϖ : S) (k : ℕ) (hk : k ≠ 0) : Val (ϖ ^ k) ↔ Val ϖ := by
  have hiff : ∀ f g : S, (∃ N, (ϖ ^ k) ^ N ∈ Ideal.span {f, g}) ↔ (∃ N, ϖ ^ N ∈ Ideal.span {f, g}) := by
    intro f g
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨k * N, by rwa [pow_mul]⟩
    · rintro ⟨N, hN⟩
      refine ⟨N, ?_⟩
      rw [← pow_mul]
      have hle : N ≤ k * N := Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hk)
      rw [← Nat.add_sub_cancel' hle, pow_add]
      exact Ideal.mul_mem_right _ _ hN
  unfold Val
  constructor
  · intro h f g hfg
    exact h f g ((hiff f g).mpr hfg)
  · intro h f g hfg
    exact h f g ((hiff f g).mp hfg)

theorem isAdicComplete_of_pow {S : Type} [CommRing S] (ϖ : S) (k : ℕ) (hk : k ≠ 0)
    (h : IsAdicComplete (Ideal.span {ϖ ^ k}) S) : IsAdicComplete (Ideal.span {ϖ}) S := by
  have hH : IsHausdorff (Ideal.span {ϖ ^ k}) S := h.toIsHausdorff
  have hP : IsPrecomplete (Ideal.span {ϖ ^ k}) S := h.toIsPrecomplete
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have H1 : IsHausdorff (Ideal.span {ϖ}) S := by
    refine ⟨fun x hx => hH.haus' x (fun n => ?_)⟩
    have := hx (k * n)
    rw [smodEq_span_iff] at this ⊢
    rwa [← pow_mul]
  have H2 : IsPrecomplete (Ideal.span {ϖ}) S := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hP.prec' (fun n => f (k * n)) (fun {m n} hmn => by
      have := hf (Nat.mul_le_mul_left k hmn)
      rw [smodEq_span_iff] at this ⊢
      rwa [← pow_mul])
    refine ⟨L, fun n => ?_⟩
    have h1 := hf (Nat.le_mul_of_pos_left n hkpos)
    have h2 := hL n
    rw [smodEq_span_iff] at h1 h2 ⊢
    rw [← pow_mul] at h2
    have h3 : ϖ ^ n ∣ f (k * n) - L := (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n hkpos)).trans h2
    have := dvd_add h1 h3
    rwa [sub_add_sub_cancel] at this
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

theorem val_pow : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 →
    (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := by
  intro S _ ϖ k hk
  exact ⟨val_pow_iff ϖ k hk, isAdicComplete_of_pow ϖ k hk⟩

end GlobalTheory.CompanionTheory.PowComp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSquares
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

lemma prod_prs_eq_iter {n : ℕ} (f : Fin n × Fin n → ℂ) :
    ∏ p ∈ prs n, f p = ∏ i : Fin n, ∏ j ∈ Ioi i, f (i, j) := by
  apply Finset.prod_finset_product
  intro p
  simp [prs]

lemma det_rev_vandermonde {n : ℕ} (v : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℂ) *
        ∏ p ∈ prs n, (v p.2 - v p.1) := by
  have h : (Matrix.of fun i j : Fin n => v i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde v).submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := by
    ext i j
    have : n - 1 - (j : ℕ) = n - (j + 1) := by omega
    simp [Matrix.vandermonde_apply, Fin.val_rev, this]
  rw [h, Matrix.det_permute', Matrix.det_vandermonde, prod_prs_eq_iter]

theorem det_vandermonde_sq {n : ℕ} (z : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det =
      (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det *
        ∏ p ∈ prs n, (z p.1 + z p.2) := by
  rw [det_rev_vandermonde (fun i => z i ^ 2), det_rev_vandermonde z, mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  ring

end GlobalTheory.CompanionTheory.CoefId
end
end

