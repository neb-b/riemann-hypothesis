module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LinDefs
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitIso

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocDefs
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

abbrev KV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v

abbrev RV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Type :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E

abbrev OV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : ValuationSubring (KV I v) :=
  v.adicCompletionIntegers I.F

def IsAdaptedFirstProjection (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v) : Prop :=
  (∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c) ∧ p1 ε = 1 ∧
    p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v ε) = 0 ∧
    ∀ x ∈ Formalism.UG.intOE I.E, p1 (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v x) ∈ OV I v

def vec1 {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v) (x : Fin I.n → RV I v) :
    Fin I.n → KV I v := fun i => p1 (x i)

def vec2 {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v) (x : Fin I.n → RV I v) :
    Fin I.n → KV I v := fun i => p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (x i))

def Lam1 (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) :
    Submodule (OV I v) (Fin I.n → KV I v) :=
  Submodule.span (OV I v) (vec1 p1 '' (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) : Set _))

def Lam2 (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) :
    Submodule (OV I v) (Fin I.n → KV I v) :=
  Submodule.span (OV I v) (vec2 p1 '' (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) : Set _))

def Pm (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) : Matrix (Fin I.n) (Fin I.n) (KV I v) :=
  I.J.map (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v))

def LinHyp (K : Type) [Field K] (O : ValuationSubring K) (n r : ℕ) (P : Matrix (Fin n) (Fin n) K) (g : K)
    (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K) (u φ u0 φ0 : Fin n → K) (t : K) : Prop :=
  g ∈ O ∧ g⁻¹ ∉ O ∧
    (∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) ∧
    (∀ i, a i ∈ Λ1 ∧ a' i ∈ Λ1 ∧ α i ∈ Λ2 ∧ α' i ∈ Λ2) ∧
    (∀ i j, pr P (α i) (a j) = 0 ∧ pr P (α' i) (a' j) = 0 ∧
      pr P (α i) (a' j) = (if i = j then 1 else 0) ∧ pr P (α' i) (a j) = (if i = j then 1 else 0)) ∧
    u ∈ Λ1 ∧ φ ∈ Λ2 ∧ u0 ∈ Λ1 ∧ φ0 ∈ Λ2 ∧
    (∀ i, pr P (α i) u = 0 ∧ pr P (α' i) u = 0 ∧ pr P φ (a i) = 0 ∧ pr P φ (a' i) = 0) ∧
    t ∈ O ∧ (∃ s ∈ O, t - 1 = g * s) ∧ pr P φ u = -t ∧
    (∀ i, (∃ s ∈ O, pr P (α i) u0 = g * s) ∧ (∃ s ∈ O, pr P (α' i) u0 = g * s) ∧
      (∃ s ∈ O, pr P φ0 (a i) = g * s) ∧ (∃ s ∈ O, pr P φ0 (a' i) = g * s)) ∧
    (∃ s ∈ O, pr P φ0 u0 + 1 = g * s)

def LinConcl (K : Type) [Field K] (O : ValuationSubring K) (n r : ℕ) (P : Matrix (Fin n) (Fin n) K) (g : K)
    (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K) (u φ u0 φ0 : Fin n → K)
    (T : GL (Fin n) K) : Prop :=
  (∀ x ∈ Λ1, (T : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1 ∧
    ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1) ∧
  (∀ β ∈ Λ2, (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K)) ∧
    (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∧
  (∀ i, (T : Matrix (Fin n) (Fin n) K) *ᵥ a i = a i ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ a' i = a' i ∧
    (α i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α i ᵥ* P ∧
    (α' i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α' i ᵥ* P) ∧
  (∃ w ∈ Λ1, ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u - u0 = g • w) ∧
  (∃ β ∈ Λ2, (φ ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) - φ0 ᵥ* P = g • (β ᵥ* P))

theorem linConcl_of (hL : LocLin) (K : Type) [Field K] (O : ValuationSubring K) (n r : ℕ)
    (P : Matrix (Fin n) (Fin n) K) (g : K) (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
    (u φ u0 φ0 : Fin n → K) (t : K) (h : LinHyp K O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 t) :
    ∃ T : GL (Fin n) K, LinConcl K O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 T := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact hL K O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

def LinData (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) (t : ℕ) : Prop :=
  LinHyp (KV I v) (OV I v) I.n r (Pm I v p1) (g : KV I v) (Lam1 I v p1) (Lam2 I v p1)
    (fun i => vec1 p1 (PI.FinKW.vecV I v (incl I (e i)))) (fun i => vec1 p1 (PI.FinKW.vecV I v (incl I (f i))))
    (fun i => vec2 p1 (PI.FinKW.vecV I v (incl I (e i)))) (fun i => vec2 p1 (PI.FinKW.vecV I v (incl I (f i))))
    (vec1 p1 (PI.FinKW.vecV I v (incl I z))) (vec2 p1 (PI.FinKW.vecV I v (incl I z)))
    (vec1 p1 (PI.FinKW.vecV I v Rf.z0)) (vec2 p1 (PI.FinKW.vecV I v Rf.z0)) (t : KV I v)

def LinOut (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (T : GL (Fin I.n) (KV I v)) : Prop :=
  LinConcl (KV I v) (OV I v) I.n r (Pm I v p1) (g : KV I v) (Lam1 I v p1) (Lam2 I v p1)
    (fun i => vec1 p1 (PI.FinKW.vecV I v (incl I (e i)))) (fun i => vec1 p1 (PI.FinKW.vecV I v (incl I (f i))))
    (fun i => vec2 p1 (PI.FinKW.vecV I v (incl I (e i)))) (fun i => vec2 p1 (PI.FinKW.vecV I v (incl I (f i))))
    (vec1 p1 (PI.FinKW.vecV I v (incl I z))) (vec2 p1 (PI.FinKW.vecV I v (incl I z)))
    (vec1 p1 (PI.FinKW.vecV I v Rf.z0)) (vec2 p1 (PI.FinKW.vecV I v Rf.z0)) T

def SumOne (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) : Prop :=
  ε + PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v ε = 1

def LocSplitP : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)), SumOne I v (PI.FinKW.psiV I v Rf.ew) →
    ∃ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1

def BridgeA : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), Hyps I g r k e f z →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal → SumOne I v (PI.FinKW.psiV I v Rf.ew) →
    ∀ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 →
    ∀ t : ℕ, t ≡ 1 [MOD g] → Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E) →
      LinData I g r k e f z Rf v p1 t

def BridgeB : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), Hyps I g r k e f z →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal → SumOne I v (PI.FinKW.psiV I v Rf.ew) →
    ∀ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 →
    ∀ T : GL (Fin I.n) (KV I v), LinOut I g r k e f z Rf v p1 T → LocConcl I g r e f z Rf.z0 v

theorem locCore_of (hS : LocSplitP) (hA : BridgeA) (hB : BridgeB) (hL : LocLin) : LocCore := by
  intro I g r k e f z Rf hH v hv hsum
  obtain ⟨p1, hp1⟩ := hS I g r k e f Rf v hsum
  obtain ⟨t, ht1, ht2⟩ := hH.2.2.2.2.2.2.2.1
  obtain ⟨T, hT⟩ := linConcl_of hL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hA I g r k e f z Rf hH v hv hsum p1 hp1 t ht1 ht2)
  exact hB I g r k e f z Rf hH v hv hsum p1 hp1 T hT

theorem target_of' (hI : LocIdem) (hS : LocSplitP) (hA : BridgeA) (hB : BridgeB) (hL : LocLin) (hG : Glue) :
    _root_.PI.ScXuExists.Target := by
  first
  | exact target_of hI (locCore_of hS hA hB hL) hG
  | exact target_of hI hG (locCore_of hS hA hB hL)
  | (unfold PI.ScXuExists.Target LocIdem Glue LocCore at *; done)

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SecondProjectionSplitEquiv
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB

open Matrix PI.UnitaryGroupMassFormula.AdIndexEq

def piHom {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K) : R →+* K × K :=
  RingHom.prod p1 (p1.comp σ)

theorem piHom_bijective {K R : Type} [Field K] [CommRing R] [Algebra K R] [FiniteDimensional K R]
    (hdim : Module.finrank K R = 2) (σ : R →+* R) (p1 : R →+* K)
    (hσK : ∀ c, σ (algebraMap K R c) = algebraMap K R c) (hσσ : ∀ r, σ (σ r) = r)
    (hp1K : ∀ c, p1 (algebraMap K R c) = c) (ε : R) (h1 : p1 ε = 1) (h0 : p1 (σ ε) = 0) :
    Function.Bijective (piHom σ p1) := by
  let L : R →ₗ[K] K × K :=
    { toFun := piHom σ p1
      map_add' := fun a b => map_add _ a b
      map_smul' := fun c r => by
        rw [Algebra.smul_def, map_mul]
        ext <;> simp [piHom, hp1K, hσK] }
  have hsurj : Function.Surjective L := by
    rintro ⟨a, b⟩
    refine ⟨algebraMap K R a * ε + algebraMap K R b * σ ε, ?_⟩
    ext <;> simp [L, piHom, hp1K, hσK, hσσ, h1, h0]
  have hfr : Module.finrank K R = Module.finrank K (K × K) := by
    rw [hdim, Module.finrank_prod, Module.finrank_self]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj, hsurj⟩

def piEquiv {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K)
    (hb : Function.Bijective (piHom σ p1)) : R ≃+* K × K :=
  RingEquiv.ofBijective (piHom σ p1) hb

theorem piEquiv_sig {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K)
    (hσσ : ∀ r, σ (σ r) = r) (hb : Function.Bijective (piHom σ p1)) (r : R) :
    piEquiv σ p1 hb (σ r) = (piEquiv σ p1 hb r).swap := by
  ext <;> simp [piEquiv, piHom, hσσ]

theorem proj_coe {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (π : R ≃+* k × k) (J : Matrix n n R) (y : Formalism.UG.UJ σ J) :
    ((SplitGL.proj σ π J y : GL n k) : Matrix n n k) = ((y : GL n R) : Matrix n n R).map (SplitGL.p1 π) := rfl

theorem isUnit_det_first_projection {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (π : R ≃+* k × k) (J : Matrix n n R) (hdet : IsUnit J.det) : IsUnit (J.map (SplitGL.p1 π)).det := by
  show IsUnit ((SplitGL.p1 π).mapMatrix J).det
  rw [← RingHom.map_det]
  exact hdet.map _

theorem second_projection_mulVec_eq {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap) (J : Matrix n n R)
    (hdet : IsUnit J.det) (y : Formalism.UG.UJ σ J) (β β' : n → k)
    (h : β' ᵥ* J.map (SplitGL.p1 π) =
      (β ᵥ* J.map (SplitGL.p1 π)) ᵥ* (((SplitGL.proj σ π J y)⁻¹ : GL n k) : Matrix n n k)) :
    ((y : GL n R) : Matrix n n R).map (SplitGL.p2 π) *ᵥ β = β' := by
  set P := J.map (SplitGL.p1 π) with hP
  set M2 := ((y : GL n R) : Matrix n n R).map (SplitGL.p2 π) with hM2
  set T := SplitGL.proj σ π J y with hT
  have hu : M2ᵀ * P * (T : Matrix n n k) = P := by
    rw [hT, proj_coe]
    exact ((SplitGL.unitary_iff σ π hπ J _).1 y.2).1
  have hTT : (T : Matrix n n k) * ((T⁻¹ : GL n k) : Matrix n n k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : M2ᵀ * P = P * ((T⁻¹ : GL n k) : Matrix n n k) := by
    calc M2ᵀ * P = M2ᵀ * P * ((T : Matrix n n k) * ((T⁻¹ : GL n k) : Matrix n n k)) := by
          rw [hTT, Matrix.mul_one]
      _ = P * ((T⁻¹ : GL n k) : Matrix n n k) := by rw [← Matrix.mul_assoc, hu]
  have h2 : (M2 *ᵥ β) ᵥ* P = β' ᵥ* P := by
    calc (M2 *ᵥ β) ᵥ* P = (β ᵥ* M2ᵀ) ᵥ* P := by rw [Matrix.vecMul_transpose]
      _ = β ᵥ* (M2ᵀ * P) := by rw [Matrix.vecMul_vecMul]
      _ = β ᵥ* (P * ((T⁻¹ : GL n k) : Matrix n n k)) := by rw [key]
      _ = (β ᵥ* P) ᵥ* ((T⁻¹ : GL n k) : Matrix n n k) := by rw [Matrix.vecMul_vecMul]
      _ = β' ᵥ* P := h.symm
  have hPu : IsUnit P.det := isUnit_det_first_projection π J hdet
  have h3 := congrArg (fun w => w ᵥ* P⁻¹) h2
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hPu, Matrix.vecMul_one] at h3
  exact h3

end PI.UnitaryGroupMassFormula.ScXuExists.BrB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitGen
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open scoped TensorProduct
open PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]

theorem exists_adapted_first_projection (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2)
    (h2K : (2 : K) ≠ 0) (ε : K ⊗[F] E) (hsum : ε + sigT σ ε = 1) (horth : ε * sigT σ ε = 0) :
    ∃ p1 : K ⊗[F] E →+* K, (∀ c : K, p1 (algebraMap K (K ⊗[F] E) c) = c) ∧ p1 ε = 1 ∧
      p1 (sigT σ ε) = 0 ∧
      ∀ r : K ⊗[F] E, r = algebraMap K (K ⊗[F] E) (p1 r) * ε +
        algebraMap K (K ⊗[F] E) (p1 (sigT σ r)) * sigT σ ε := by
  classical
  have hσT : ∀ x : K ⊗[F] E, sigT σ (sigT σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp [sigT, hσσ]
    | add x y hx hy => simp [map_add (f := _), hx, hy]
  have hσA : ∀ c : K, sigT σ (algebraMap K (K ⊗[F] E) c) = algebraMap K (K ⊗[F] E) c := by
    intro c
    simp [sigT, Algebra.TensorProduct.algebraMap_apply]
  have hε2 : ε * ε = ε := by
    calc ε * ε = ε * (ε + sigT σ ε) - ε * sigT σ ε := by ring
      _ = ε := by rw [hsum, horth, mul_one, sub_zero]
  have hfr : Module.finrank K (K ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, h2]
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K (K ⊗[F] E) := inferInstance
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hε0 : ε ≠ 0 := by
    intro h0
    rw [h0, map_zero, add_zero] at hsum
    exact zero_ne_one hsum
  have hδ0 : sigT σ ε ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hsum
    rw [hsum, map_one] at h0
    exact one_ne_zero h0
  have hrn := LinearMap.finrank_range_add_finrank_ker (LinearMap.mulRight K ε)
  rw [hfr] at hrn
  have hker : Module.finrank K (LinearMap.ker (LinearMap.mulRight K ε)) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro h
    apply hδ0
    apply h
    rw [LinearMap.mem_ker, LinearMap.mulRight_apply, mul_comm, horth]
  have hmemε : ε ∈ LinearMap.range (LinearMap.mulRight K ε) :=
    ⟨ε, by rw [LinearMap.mulRight_apply, hε2]⟩
  have hran : Module.finrank K (LinearMap.range (LinearMap.mulRight K ε)) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro h
    exact hε0 (h ε hmemε)
  have h1 : Module.finrank K (LinearMap.range (LinearMap.mulRight K ε)) = 1 := by omega
  have hex : ∀ r : K ⊗[F] E, ∃ c : K, algebraMap K (K ⊗[F] E) c * ε = r * ε := by
    intro r
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨ε, hmemε⟩ : LinearMap.range (LinearMap.mulRight K ε))
      (fun h => hε0 (congrArg Subtype.val h))).mp h1 ⟨r * ε, ⟨r, rfl⟩⟩
    refine ⟨c, ?_⟩
    rw [← Algebra.smul_def]
    exact congrArg Subtype.val hc
  have huniq : ∀ c d : K, algebraMap K (K ⊗[F] E) c * ε = algebraMap K (K ⊗[F] E) d * ε →
      c = d := by
    intro c d h
    rw [← Algebra.smul_def, ← Algebra.smul_def, ← sub_eq_zero, ← sub_smul] at h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hε0)
  choose p hp using hex
  have hpu : ∀ r c, algebraMap K (K ⊗[F] E) c * ε = r * ε → p r = c :=
    fun r c h => huniq _ _ ((hp r).trans h.symm)
  let p1 : K ⊗[F] E →+* K :=
    { toFun := p
      map_one' := hpu 1 1 (by rw [map_one])
      map_mul' := fun r s => hpu (r * s) (p r * p s) (by
        rw [map_mul, mul_assoc, hp s, mul_left_comm, hp r, ← mul_assoc, mul_comm s r])
      map_zero' := hpu 0 0 (by rw [map_zero])
      map_add' := fun r s => hpu (r + s) (p r + p s) (by
        rw [map_add (f := _), add_mul, hp r, hp s, add_mul]) }
  refine ⟨p1, fun c => hpu _ c rfl, hpu _ 1 (by rw [map_one, one_mul, hε2]),
    hpu _ 0 (by rw [map_zero, zero_mul, mul_comm, horth]), fun r => ?_⟩
  have h2' : algebraMap K (K ⊗[F] E) (p (sigT σ r)) * sigT σ ε = r * sigT σ ε := by
    have h3 : sigT σ (algebraMap K (K ⊗[F] E) (p (sigT σ r)) * ε) = sigT σ (sigT σ r * ε) := by
      rw [hp (sigT σ r)]
    rwa [map_mul, map_mul, hσA, hσT] at h3
  show r = algebraMap K _ (p r) * ε + algebraMap K _ (p (sigT σ r)) * sigT σ ε
  rw [hp r, h2', ← mul_add, hsum, mul_one]

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

