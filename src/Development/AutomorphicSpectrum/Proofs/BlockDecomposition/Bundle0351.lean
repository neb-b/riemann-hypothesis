module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import GroundTheory.LocalFields.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import GroundTheory.AutomorphicForms.SmoothRep
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (n : ℕ) (N : ℤ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ i, x.toAdd i ∈ valBall k N}
  mul_mem' := by
    intro a b ha hb i
    simpa using add_mem (ha i) (hb i)
  one_mem' := by
    intro i
    simp
  inv_mem' := by
    intro a ha i
    simpa using neg_mem (ha i)

theorem mem_box {n : ℕ} {N : ℤ} {x : Multiplicative (Fin n → k)} :
    x ∈ box k n N ↔ ∀ i, x.toAdd i ∈ valBall k N := Iff.rfl

theorem box_antitone (n : ℕ) {M N : ℤ} (h : M ≤ N) : box k n N ≤ box k n M :=
  fun _ hx i => valBall_antitone h (hx i)

def chi (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) : Multiplicative (Fin n → k) →* ℂˣ where
  toFun x := Circle.toUnits (ψ (a ⬝ᵥ x.toAdd))
  map_one' := by simp
  map_mul' x y := by simp [dotProduct_add, AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (x : Multiplicative (Fin n → k)) :
    chi k ψ a x = Circle.toUnits (ψ (a ⬝ᵥ x.toAdd)) := rfl

abbrev chiOn (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (H : Subgroup (Multiplicative (Fin n → k))) :
    H →* ℂˣ := (chi k ψ a).comp H.subtype

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun x => MirU_le_Mir k n ⟨x, rfl⟩)

@[simp] theorem coe_unipMir (n : ℕ) (x : Multiplicative (Fin n → k)) :
    ((unipMir k n x : Mir k n) : GL (Fin (n + 1)) k) = unip k n x := rfl

variable {k}

theorem exists_unipMir {n : ℕ} (u : MirUin k n) : ∃ x, unipMir k n x = (u : Mir k n) := by
  obtain ⟨x, hx⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  exact ⟨x, Subtype.ext hx⟩

theorem mem_chi_zero {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (τ : Representation ℂ (Mir k (m + 1)) V) {w : V} (hw : w ∈ twKer τ (MirUin k (m + 1)) 1) :
    w ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤ (chiOn k ψ 0 ⊤) := by
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨u, w, rfl⟩
  obtain ⟨x, hx⟩ := exists_unipMir u
  refine Submodule.subset_span ⟨⟨x, trivial⟩, w, ?_⟩
  simp [chi_apply, hx]

theorem mem_chi_row {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (τ : Representation ℂ (Mir k (m + 1)) V) (g : GL (Fin (m + 1)) k) {w : V}
    (hw : w ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) :
    τ (levi k (m + 1) g⁻¹) w ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤
      (chiOn k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⊤) := by
  have hle : twKer τ (MirUin k (m + 1)) (mirChar k ψ m) ≤
      (twKer (τ.comp (unipMir k (m + 1))) ⊤
        (chiOn k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⊤)).comap
        (τ (levi k (m + 1) g⁻¹)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    obtain ⟨x, hx⟩ := exists_unipMir u
    set y : Multiplicative (Fin (m + 1) → k) :=
      Multiplicative.ofAdd (((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec x.toAdd)
      with hy
    have hconj : levi k (m + 1) g⁻¹ * (u : Mir k (m + 1)) = unipMir k (m + 1) y * levi k (m + 1) g⁻¹ := by
      apply Subtype.ext
      show glEmb k (m + 1) g⁻¹ * ((u : Mir k (m + 1)) : GL (Fin (m + 2)) k) = unip k (m + 1) y * glEmb k (m + 1) g⁻¹
      rw [← hx, coe_unipMir, glEmb_mul_unip']
    have hchar : mirChar k ψ m u = chi k ψ (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) y := by
      rw [mirChar_eq k ψ m u x (by rw [← hx]; rfl), chi_apply]
      congr 2
      have : (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) ⬝ᵥ y.toAdd =
          ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec y.toAdd) (Fin.last m) := rfl
      rw [this, hy, toAdd_ofAdd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, hconj, map_mul,
      Module.End.mul_apply, hchar]
    exact Submodule.subset_span ⟨⟨y, trivial⟩, τ (levi k (m + 1) g⁻¹) w, rfl⟩
  exact hle hw

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteGenerator
section
open Matrix Finset
open PositivityTheory.RgBcC.RealD (epow gelA)

namespace GlobalTheory.CompanionTheory.ModelS

theorem epow_eq_pow_of {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero =>
      change (if a = b then 1 else 0) = _
      simp only [pow_zero, Matrix.one_apply]
  | succ m ih =>
      change (∑ c, E a c * epow E m c b) = _
      simp only [pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem gelA_central : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E →
    ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  intro n V _ _ E hE m a b
  rw [eq_comm, ← sub_eq_zero]
  delta gelA
  simp only [epow_eq_pow_of]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [GlobalTheory.SmoothForms.comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteOfCommute
section
open scoped BigOperators
open PositivityTheory.RgBcC.RealD (epow gelA)

namespace GlobalTheory.CompanionTheory.ModelS

theorem commute_epow_of_units {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V)
    (hT : ∀ a b, T * E a b = E a b * T) (m : ℕ) (a b : Fin n) :
    Commute T (epow E m a b) := by
  induction m generalizing a b with
  | zero =>
    change Commute T (if a = b then 1 else 0)
    split_ifs
    · exact Commute.one_right T
    · exact Commute.zero_right T
  | succ m ih =>
    change Commute T (∑ c, E a c * epow E m c b)
    exact Commute.sum_right _ _ _ fun c _ => Commute.mul_right (hT a c) (ih c b)

theorem gelA_commute_of_units : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V),
    (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m := by
  intro n V _ _ E T hT m
  have h : Commute T (gelA E m) :=
    Commute.sum_right _ _ _ fun a _ => commute_epow_of_units E T hT m a a
  exact h.eq.symm

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantEvalLowest
section
open Finset
open PositivityTheory.RgBcC.RealD (epow gelA)

noncomputable section

namespace GlobalTheory.CompanionTheory.EvGel

section Dual

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def dualFam (E : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ (Module.Dual ℂ V) :=
  fun a b => (E b a).dualMap

theorem dualFam_apply (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    dualFam E a b φ v = φ (E b a v) := rfl

theorem glRel_dualFam {E : Fin n → Fin n → Module.End ℂ V} (hE : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (dualFam E) := by
  intro a b c d
  refine LinearMap.ext fun φ => LinearMap.ext fun v => ?_
  have h2 := congrArg (fun T : Module.End ℂ V => φ (T v)) (hE d c b a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dualFam_apply]
  by_cases h1 : b = c <;> by_cases h3 : d = a
  · subst h1; subst h3; simpa [dualFam_apply] using h2
  · subst h1; simpa [dualFam_apply, h3, Ne.symm h3] using h2
  · subst h3; simpa [dualFam_apply, h1, Ne.symm h1] using h2
  · simpa [dualFam_apply, h1, h3, Ne.symm h1, Ne.symm h3] using h2

theorem pow_dualFam (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    ((Matrix.of (dualFam E) : Matrix (Fin n) (Fin n) (Module.End ℂ (Module.Dual ℂ V))) ^ m) a b φ v =
      φ (((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) b a v) := by
  induction m generalizing a b φ v with
  | zero =>
    by_cases h : a = b
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  | succ m ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pow_succ', pow_succ, Matrix.mul_apply, Matrix.mul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
      LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Module.End.mul_apply, Matrix.of_apply, dualFam_apply, ih]

end Dual

theorem epow_eq_pow {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp only [epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem ev_gelA : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ),
    (∀ a b, b < a → ∀ v, ev (E a b v) = 0) → (∀ a v, ev (E a a v) = x a * ev v) →
    ∀ (m : ℕ) (v : V), ev (gelA E m v) =
      GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v := by
  intro n V _ _ E hE ev x hlow hdiag m v
  have hHW : Formalism.REAL.IsHW (dualFam E) x ev :=
    ⟨fun a => LinearMap.ext fun w => by simp [dualFam_apply, hdiag],
      fun a b hab => LinearMap.ext fun w => by simpa [dualFam_apply] using hlow b a hab w⟩
  have h1 := GlobalTheory.PhiEigenfun.trace_pow_hw (dualFam E) x ev (glRel_dualFam hE) hHW m
  have h2 := congrArg (fun φ : Module.Dual ℂ V => φ v) h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pow_dualFam, smul_eq_mul] at h2
  have hval : GlobalTheory.Dec.gelfVal (fun a : Fin n => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m =
      ∑ a, ∑ b, (Formalism.REAL.Amat (Formalism.REAL.lsh x) ^ m) a b := by
    have : (fun c : Fin n => x c + ((n : ℂ) - 1) / 2 - ((c : ℕ) : ℂ) + ((n : ℂ) - 1) / 2) = Formalism.REAL.lsh x := by
      funext c
      simp only [Formalism.REAL.lsh]
      ring
    rw [GlobalTheory.Dec.gelfVal, this]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hval, ← h2, gelA, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [epow_eq_pow]

end GlobalTheory.CompanionTheory.EvGel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaW

def revMat (A : Type) [CommRing A] (N : ℕ) : Matrix (Fin N) (Fin N) A :=
  (1 : Matrix (Fin N) (Fin N) A).submatrix Fin.rev id

theorem revMat_mul {A : Type} [CommRing A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) :
    revMat A N * M = M.submatrix Fin.rev id := by
  ext i j
  simp [revMat, Matrix.mul_apply, Matrix.one_apply]

theorem mul_revMat {A : Type} [CommRing A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) :
    M * revMat A N = M.submatrix id Fin.rev := by
  ext i j
  simp only [revMat, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro b _ hb
    rw [if_neg, mul_zero]
    intro h
    exact hb (by rw [← h, Fin.rev_rev])
  · simp

theorem revMat_mul_self (A : Type) [CommRing A] (N : ℕ) : revMat A N * revMat A N = 1 := by
  rw [revMat_mul]
  ext i j
  simp [revMat, Matrix.one_apply]

def w₀ (A : Type) [CommRing A] (N : ℕ) : GL (Fin N) A :=
  ⟨revMat A N, revMat A N, revMat_mul_self A N, revMat_mul_self A N⟩

theorem thetaW_eq_conj (A : Type) [CommRing A] (N : ℕ) (g : GL (Fin N) A) :
    thetaW A N g = w₀ A N * invT g * (w₀ A N)⁻¹ := by
  apply Units.ext
  show _ = revMat A N * (invT g).1 * revMat A N
  rw [revMat_mul, mul_revMat]
  ext i j
  simp [thetaW, Matrix.reindexAlgEquiv_apply]

def compInvTEquiv {A : Type} [CommRing A] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) A) V) :
    Representation.Equiv (π.comp invT) (π.comp (thetaW A N)) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear (π (w₀ A N)) (π (w₀ A N)⁻¹)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl))
    fun g => LinearMap.ext fun v => by
      show π (w₀ A N) (π (invT g) v) = π (thetaW A N g) (π (w₀ A N) v)
      rw [thetaW_eq_conj, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel_right]

theorem comp_thetaW_equiv_contra : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GKLocal k → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  intro k _ _ _ _ hGK N V _ _ π hs hi
  obtain ⟨e⟩ := hGK N π hs hi
  exact ⟨(compInvTEquiv π).symm.trans e⟩

end GlobalTheory.CompanionTheory.ThetaW

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorExists
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeKm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_span_unif_pow_iff (m : ℕ) (a : 𝒪[k]) :
    a ∈ Ideal.span {Zls.unif k ^ m} ↔ (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (a : k) ∈ 𝒪[k] := by
  have hc : (((Zls.unifU k ^ m : kˣ)) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k) := by
    simp [Zls.unifU]
    rfl
  have hne : ((Zls.unif k ^ m : 𝒪[k]) : k) ≠ 0 := by
    rw [← hc]; exact Units.ne_zero _
  have hinv : (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hc]
  rw [Ideal.mem_span_singleton', hinv]
  constructor
  · rintro ⟨b, rfl⟩
    have : ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * ((b * Zls.unif k ^ m : 𝒪[k]) : k) = (b : k) := by
      rw [MulMemClass.coe_mul]
      field_simp
    rw [this]
    exact b.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul]
    change ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * (a : k) * _ = _
    field_simp

theorem mem_Km_iff {N m : ℕ} (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ g ∈ KO k (Fin N) ∧
      ∀ i j, (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j ∈ 𝒪[k] := by
  have key : ∀ (u : GL (Fin N) 𝒪[k]) (i j : Fin N),
      ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) u).val - 1) i j =
        ((u.val i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j : 𝒪[k]) : k) := by
    intro u i j
    by_cases h : i = j
    · subst h
      simp [Matrix.GeneralLinearGroup.map_apply]
      rfl
    · simp [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply_ne h]
      rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq]
    have h := congrArg (fun x : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) => x.val i j)
      (MonoidHom.mem_ker.1 hu)
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, MonoidHom.mem_ker.2 (Units.ext (Matrix.ext fun i j => ?_)), rfl⟩
    have h' := h i j
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq] at h'
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h'

theorem continuous_entry_Km (N : ℕ) (c : k) (i j : Fin N) :
    Continuous fun g : GL (Fin N) k => c * (g.val - 1) i j :=
  continuous_const.mul
    (((Units.continuous_val (M := Matrix (Fin N) (Fin N) k)).sub continuous_const).matrix_elem i j)

theorem coe_Km_eq (N m : ℕ) :
    (Zls.Km k N m : Set (GL (Fin N) k)) = (KO k (Fin N) : Set (GL (Fin N) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin N) k => (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j) ⁻¹'
        (𝒪[k] : Set k) := by
  ext g
  simp only [SetLike.mem_coe, mem_Km_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (show IsOpen (𝒪[k] : Set k) from Valuation.isOpen_integer).preimage (continuous_entry_Km N _ i j))

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
    (show IsCompact (𝒪[k] : Set k) from IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed.preimage
      (continuous_entry_Km N _ i j))

theorem totallyDisconnected_GL (N : ℕ) : TotallyDisconnectedSpace (GL (Fin N) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  exact ⟨(GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := Fin N)).isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem exists_isHeckeOp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    ∀ (m : ℕ) (g : GL (Fin N) k), ∃ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m g T := by
  intro k _ _ _ _ N V _ _ π hπ m g
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI := totallyDisconnected_GL (k := k) N
  have hKc := isCompact_Km (k := k) N m
  have hKo := isOpen_Km (k := k) N m
  have hπ' : GroundTheory.Automorphic.IsSmooth π := fun v => hπ v
  have hfix : ∀ w : GroundTheory.Automorphic.fixedVectors π (Zls.Km k N m),
      (w : V) ∈ fixed π (Zls.Km k N m) := fun w h => by
    simpa using w.2 h h.2
  refine ⟨LinearMap.codRestrict (fixed π (Zls.Km k N m))
    ((Submodule.subtype _) ∘ₗ GroundTheory.Automorphic.fixedProj π hπ' hKc hKo ∘ₗ π g ∘ₗ
      (fixed π (Zls.Km k N m)).subtype) fun v => hfix _, ?_⟩
  intro v l hl
  have hs := GroundTheory.Automorphic.sub_fixedProj_mem hπ' hKc hKo (π g (v : V))
  have h0 := GroundTheory.Automorphic.coinvariantsKer_le_ker_of_invariant (ρ := π) (K := Zls.Km k N m) (f := l)
    (fun x hx w => LinearMap.congr_fun (hl x hx) w) hs
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.CompanionTheory.HeckeKm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsClassificationOrderFreeEquiv
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LUniq

theorem isL_unique : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    LOrderFree k → ∀ (𝔭 : Multiset (Segment k)) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W),
    IsL 𝔭 π → IsL 𝔭 σ → Nonempty (π.Equiv σ) := by
  intro k _ _ _ _ hLO 𝔭 N V W _ _ _ _ π σ hπ hσ
  obtain ⟨h, x, hd, hx, hπc⟩ := hπ
  have hσc : IsCosocle σ (prodIrr x hd) := hLO 𝔭 h N x hd hx σ hσ
  exact hσc.unique hπc

end GlobalTheory.CompanionTheory.LUniq
end

