module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.IwSplitFrame

section Frame

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

end Frame

theorem exists_compl {K : Type} [Field K] [CharZero K] {n r : ℕ} (e e' : Matrix (Fin n) (Fin r) K)
    (p a : Matrix (Fin r) (Fin n) K) (hpe : p * e = 1) (hpe' : p * e' = 0) (hae : a * e = 0) (hae' : a * e' = 1) :
    ∃ (k : ℕ) (i : Matrix (Fin n) (Fin k) K) (q : Matrix (Fin k) (Fin n) K), n = r + k + r ∧
      e * p + i * q + e' * a = 1 := by
  set π : Matrix (Fin n) (Fin n) K := 1 - e * p - e' * a with hπdef
  have hXX : e * p * (e * p) = e * p := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc p, hpe, Matrix.one_mul]
  have hXY : e * p * (e' * a) = 0 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc p, hpe', Matrix.zero_mul, Matrix.mul_zero]
  have hYX : e' * a * (e * p) = 0 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, hae, Matrix.zero_mul, Matrix.mul_zero]
  have hYY : e' * a * (e' * a) = e' * a := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, hae', Matrix.one_mul]
  have hπ : π * π = π := by
    simp only [hπdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hXX, hXY, hYX, hYY]
    abel
  have hid : IsIdempotentElem (Matrix.toLin' π) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hπ]
  set W := LinearMap.range (Matrix.toLin' π)
  set b := Module.finBasis K W
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ (Matrix.toLin' π).rangeRestrict), ?_, ?_⟩
  · have h1 := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
    rw [Matrix.trace_toLin'_eq, hπdef, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm e,
      Matrix.trace_mul_comm e', hpe, hae', Matrix.trace_one, Matrix.trace_one] at h1
    simp only [Fintype.card_fin] at h1
    have h2 : ((r + Module.finrank K W + r : ℕ) : K) = n := by push_cast; rw [← h1]; ring
    exact (Nat.cast_injective h2).symm
  · rw [← LinearMap.toMatrix'_comp]
    have h3 : (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ (Matrix.toLin' π).rangeRestrict) =
        Matrix.toLin' π := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply,
        LinearMap.rangeRestrict, LinearMap.codRestrict_apply]
    rw [h3, LinearMap.toMatrix'_toLin', hπdef]
    abel

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mat_mul (g h : GLoc σ J v) : (HA.mat (F := F) (Fv F v) σ J (g * h)).1 =
    (HA.mat (F := F) (Fv F v) σ J g).1 * (HA.mat (F := F) (Fv F v) σ J h).1 := by
  rw [← GlobalTheory.AdelicU.matHom_apply, ← GlobalTheory.AdelicU.matHom_apply, ← GlobalTheory.AdelicU.matHom_apply, map_mul, Units.val_mul]

theorem mat_one : (HA.mat (F := F) (Fv F v) σ J 1).1 = 1 := by
  rw [← GlobalTheory.AdelicU.matHom_apply, map_one, Units.val_one]

def keepGrp (j : Matrix (Fin n) (Fin r) (Fv F v ⊗[F] E)) : Subgroup (GLoc σ J v) where
  carrier := {q | ∃ β : GL (Fin r) (Fv F v ⊗[F] E), (HA.mat (F := F) (Fv F v) σ J q).1 * j = j * β.1}
  mul_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨β', hβ'⟩
    refine ⟨β * β', ?_⟩
    rw [mat_mul, Matrix.mul_assoc, hβ', ← Matrix.mul_assoc, hβ, Units.val_mul, Matrix.mul_assoc]
  one_mem' := ⟨1, by rw [mat_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  inv_mem' := by
    rintro a ⟨β, hβ⟩
    refine ⟨β⁻¹, ?_⟩
    have h1 : (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * (HA.mat (F := F) (Fv F v) σ J a).1 = 1 := by
      rw [← mat_mul, inv_mul_cancel, mat_one]
    calc (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * j
        = (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * (j * β.1) * (β⁻¹).1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc j, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = j * (β⁻¹).1 := by rw [← hβ, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem keeps_of_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) {e : Matrix (Fin n) (Fin r) E}
    {p : Matrix (Fin r) (Fin n) E} (hp : p * e = 1) {a a' : Matrix (Fin r) (Fin r) (Fv F v)}
    (h1 : (splitHom σ J τ g).1 * e.map τ = e.map τ * a)
    (h2 : (splitHom σ J (τ.comp σ) g).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a') :
    g ∈ keepGrp (σ := σ) (J := J) (v := v) (e.map (inclR (F := F) (Fv F v))) := by
  set j := e.map (inclR (F := F) (Fv F v))
  set P := p.map (inclR (F := F) (Fv F v))
  have hP : P * j = 1 := by
    rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ (t : E →ₐ[F] Fv F v) {b : Matrix (Fin r) (Fin r) (Fv F v)},
      (splitHom σ J t g).1 * e.map t = e.map t * b →
      (HA.mat (F := F) (Fv F v) σ J g).1.map ((splitProj t).toRingHom) * j.map ((splitProj t).toRingHom) =
        j.map ((splitProj t).toRingHom) * b := fun t b hb => by
    have e2 : j.map ((splitProj t).toRingHom) = e.map t := by
      ext k l
      simp [j, splitProj_inclR]
    rw [e2]
    exact hb
  have hk : (HA.mat (F := F) (Fv F v) σ J g).1 * j = j * (P * ((HA.mat (F := F) (Fv F v) σ J g).1 * j)) := by
    ext k l
    exact split_ext h τ (congrFun (congrFun (GlobalTheory.Core.Rk.IwFlagSplit.map_keeps _ hP (key τ h1)) k) l)
      (congrFun (congrFun (GlobalTheory.Core.Rk.IwFlagSplit.map_keeps _ hP (key _ h2)) k) l)
  have hk' : (HA.mat (F := F) (Fv F v) σ J g⁻¹).1 * (HA.mat (F := F) (Fv F v) σ J g).1 = 1 := by
    rw [← mat_mul, inv_mul_cancel, mat_one]
  have h3 : (P * ((HA.mat (F := F) (Fv F v) σ J g⁻¹).1 * j)) * (P * ((HA.mat (F := F) (Fv F v) σ J g).1 * j)) = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc (HA.mat (F := F) (Fv F v) σ J g⁻¹).1, ← hk,
      ← Matrix.mul_assoc (HA.mat (F := F) (Fv F v) σ J g⁻¹).1, hk', Matrix.one_mul, hP]
  exact ⟨⟨_, _, mul_eq_one_comm.1 h3, h3⟩, hk⟩

end Local

end GlobalTheory.IwSplitFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGaussianVacuaSpanOfVacuumEquations
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_realAd_mul (t : ℝ) (c : AF F) : evI F (realAd F t * c) = t • evI F c := by
  rw [← evIHom_apply, map_mul, evIHom_apply, evIHom_apply, Algebra.smul_def]
  congr 1
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem realAd_mul_snd (t : ℝ) (c : AF F) : (realAd F t * c).2 = 0 := by
  show (realAd F t).2 * c.2 = 0
  simp [realAd]

theorem at_realAd_mul (t : ℝ) (c : AF F) : At (evI F) (realAd F t * c) := by
  intro b hb
  have h1 : b.1 = 0 := by
    have : InfiniteAdeleRing.ringEquiv_mixedSpace F b.1 = 0 := hb
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  rw [smul_eq_mul, ← mul_assoc]
  have : b * realAd F t = 0 := Prod.ext (by show b.1 * _ = 0; rw [h1, zero_mul]) (by show _ * (realAd F t).2 = 0; simp [realAd])
  rw [this, zero_mul]

def gam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (t : ℝ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * Algebra.trace ℝ _ (y ⬝ᵥ fun i => evI F (w.2 i)) + t ^ 2 * Algebra.trace ℝ _ (evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) : ℝ) : ℂ)) *
    f (y + t • fun i => evI F (w.1 i))

theorem gam_differentiableAt (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    DifferentiableAt ℝ (fun t => gam w f t y) 0 := by
  unfold gam
  fun_prop

theorem schr_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (t : ℝ) (f : SInf F κ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    schr ψ (realAd F t • w) (pureA F f g) x = gam w f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  have hK : x ⬝ᵥ (realAd F t • w).2 + ⅟(2 : AF F) * ((realAd F t • w).1 ⬝ᵥ (realAd F t • w).2) =
      realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have hev : evI F (realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)))) =
      t • ((fun i => evI F (x i)) ⬝ᵥ (fun i => evI F (w.2 i)) + t • evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    rw [evI_realAd_mul]
    congr 1
    rw [← evIHom_apply, map_add (f := _), evIHom_apply, evIHom_apply, evI_realAd_mul, ← evIHom_apply (x ⬝ᵥ w.2),
      RingHom.map_dotProduct]
    rfl
  unfold schr pureA gam
  rw [hK, hψ.2.2 _ (at_realAd_mul _ _), hev]
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + (realAd F t • w).1) i).1) =
      (fun i => evI F (x i)) + t • fun i => evI F (w.1 i) := by
    funext i
    show evIHom (x i + realAd F t * w.1 i) = evI F (x i) + t • evI F (w.1 i)
    rw [map_add (f := _), evIHom_apply, evIHom_apply, evI_realAd_mul]
  have hg : (fun i => ((x + (realAd F t • w).1) i).2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + (realAd F t * w.1 i).2 = (x i).2
    rw [realAd_mul_snd, add_zero]
  rw [hf, hg]
  simp only [map_smul, map_add (f := _), smul_eq_mul]
  ring_nf

end GlobalTheory.VacFactor

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def dgam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  deriv (fun t => gam w f t y) 0

theorem exists_indep {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (m : ℕ) (f : Fin m → SInf F κ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ k, g k ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ LinearIndependent ℂ g ∧ Φ = ∑ k, pureA F (f k) (g k) := by
  obtain ⟨m₀, c, p, hp⟩ := Submodule.mem_span_set'.mp hΦ
  choose f₀ g₀ hg₀ hp₀ using fun i => (p i).2
  set f₁ : Fin m₀ → SInf F κ := fun i => c i • f₀ i
  have hΦ' : Φ = ∑ i, pureA F (f₁ i) (g₀ i) := by
    rw [← hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hp₀ i]
    funext x
    simp [f₁, pureA, mul_assoc]
  set V := Submodule.span ℂ (Set.range g₀)
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range g₀)
  let b := Module.finBasis ℂ V
  have hmem : ∀ i, g₀ i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  let a : Fin m₀ → Fin (Module.finrank ℂ V) → ℂ := fun i j => b.repr ⟨g₀ i, hmem i⟩ j
  have hg : ∀ i z, g₀ i z = ∑ j, a i j * (b j : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z := by
    intro i z
    have := congrArg (fun v : V => (v : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z) (b.sum_repr ⟨g₀ i, hmem i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine ⟨Module.finrank ℂ V, fun j => ∑ i, a i j • f₁ i, fun j => (b j : _), fun j => ?_, ?_, ?_⟩
  · exact (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hg₀ i)) (b j).2
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · rw [hΦ']
    funext x
    simp only [Finset.sum_apply, pureA, hg, Finset.mul_sum, Finset.sum_mul, SchwartzMap.sum_apply,
      SchwartzMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (t : ℝ) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    M.heisLine ψ u t (pureA F f g) x = gam (M.co.e u) f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  unfold Model.heisLine Darboux.rho
  rw [map_smul, schr_pureA ψ hψ]

theorem hasDerivAt_heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (pureA F f g) x)
      (dgam (M.co.e u) f (fun i => evI F (x i)) * g (fun i => (x i).2)) 0 := by
  simp only [heisLine_pureA M ψ hψ]
  exact (gam_differentiableAt _ _ _).hasDerivAt.mul_const _

theorem hasDerivAt_heisLine_sum (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (g : Fin m → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x)
      (∑ k, dgam (M.co.e u) (f k) (fun i => evI F (x i)) * g k (fun i => (x i).2)) 0 := by
  have e : (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x) =
      fun t => ∑ k, M.heisLine ψ u t (pureA F (f k) (g k)) x := by
    funext t
    simp only [Model.heisLine, Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]
  rw [e]
  exact HasDerivAt.fun_sum fun k _ => hasDerivAt_heisLine_pureA M ψ hψ u (f k) (g k) x

end GlobalTheory.VacFactor


open GlobalTheory.VacFactor in
theorem GlobalTheory.VacFactor.mem_span_of_isGaussEq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), GlobalTheory.VacDatum.IsGaussEq M ψ τ Φ →
      Φ ∈ Submodule.span ℂ {Φ' | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ),
        f ∈ M.Pol ψ τ ∧ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ Φ' = GlobalTheory.WeilM.pureA F f g} := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hψ Φ hΦ hG
  obtain ⟨m, f, g, hg, hgi, rfl⟩ := exists_indep hΦ
  obtain ⟨ε, hε⟩ := hG
  let mk : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) →
      (Fin n × Fin d → AF F) :=
    fun y z i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), z i)
  have hmk1 : ∀ y z, (fun i => evI F (mk y z i)) = y := fun y z => by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  have hmk2 : ∀ y z, (fun i => (mk y z i).2) = z := fun y z => rfl
  have key : ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
      (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
      ∀ k y, dgam (M.co.e u') (f k) y = Complex.I * dgam (M.co.e u) (f k) y := by
    intro u u' hu hu' hr k y
    have h0 : ∑ k, (dgam (M.co.e u') (f k) y - Complex.I * dgam (M.co.e u) (f k) y) • g k = 0 := by
      funext z
      have e := hε u u' hu hu' hr (mk y z)
      rw [(hasDerivAt_heisLine_sum M ψ hψ u' f g (mk y z)).deriv,
        (hasDerivAt_heisLine_sum M ψ hψ u f g (mk y z)).deriv, hmk1, hmk2] at e
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
      rw [e, Finset.mul_sum]
      simp only [mul_assoc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hgi _ h0 k)
  have hgne : ∀ k, ∃ z, g k z ≠ 0 := fun k => by
    by_contra h
    push Not at h
    exact hgi.ne_zero k (funext h)
  have gauss : ∀ k, M.IsGauss ψ τ (f k) := by
    intro k
    obtain ⟨z₀, hz₀⟩ := hgne k
    refine ⟨ε, fun u u' hu hu' hr f₁ f₁' h1 h1' => ?_⟩
    have hR : Rest (evI F) (⇑(f k)) (fun x : Fin n × Fin d → AF F => g k (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f k, g k, hg k, rfl⟩⟩
      have hz2 : ∀ i, (z i).2 = 0 := by
        intro i
        have h0 : evI F (show AF F from ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))) = 0 := by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _
        have := congrArg (fun v : Fin n × Fin d → AF F => (v i).2) (hz _ h0)
        change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at this
        simpa using this
      have hxz : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
        funext i
        show (x i).2 + (z i).2 = (x i).2
        rw [hz2, add_zero]
      exact congrArg (g k) hxz
    have hD : ∀ (v : Matrix (Fin n) (Fin d) (AE F E)) (f₂ : SInf F (Fin n × Fin d)),
        ActsD (evI F) (M.heisLine ψ v) (⇑(f k)) (⇑f₂) → ∀ y, f₂ y = dgam (M.co.e v) (f k) y := by
      intro v f₂ h y
      have a := h _ hR (mk y z₀)
      have b := hasDerivAt_heisLine_pureA M ψ hψ v (f k) (g k) (mk y z₀)
      have := a.unique b
      simp only [tens, hmk1, hmk2] at this
      exact mul_right_cancel₀ hz₀ this
    refine DFunLike.ext _ _ fun y => ?_
    rw [hD u' f₁' h1' y, key u u' hu hu' hr k y, ← hD u f₁ h1 y]
    simp
  refine Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨f k, g k, ?_, hg k, rfl⟩
  exact Submodule.mem_sInf.mpr fun N hN => hN.1 _ (gauss k)

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIdealSmulAdelicPointRationalLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepLatIdeal

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem smul_mem_of_mem_smul (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (a : E)
    (ha : ∀ m ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E m * a) (x : Fin n → E) (hx : x ∈ 𝔪 • Λ) :
    a • x ∈ Λ := by
  refine Submodule.smul_induction_on (p := fun w => a • w ∈ Λ) hx (fun m hm y hy => ?_) (fun u v hu hv => ?_)
  · obtain ⟨c, hc⟩ := ha m hm
    have e : a • (m • y) = c • y := by
      rw [← algebraMap_smul E m y, ← algebraMap_smul E c y, smul_smul, hc, mul_comm]
    simp only [e]
    exact Λ.smul_mem c hy
  · simp only [smul_add]
    exact Λ.add_mem hu hv

theorem smul_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (a : E)
    (ha : ∀ m ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E m * a)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) • z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    have hax := smul_mem_of_mem_smul Λ 𝔪 a ha x hx
    change _ ∈ Submodule.span _ _
    refine Submodule.subset_span ⟨a • x, hax, ?_⟩
    funext i
    show (a • x) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (x i ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [smul_add]; exact Submodule.add_mem _ hu hv
  | smul s u _ hu =>
    rw [Subring.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ s hu

theorem eq_zero_of_mem_hatL_bot (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (⊥ : Submodule (𝓞 E) (Fin n → E))) : z = 0 := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    have hx0 : x = 0 := (Submodule.mem_bot _).1 hx
    subst hx0
    funext i
    show (0 : E) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = 0
    exact TensorProduct.zero_tmul _ _
  | zero => rfl
  | add u v _ _ hu hv => rw [hu, hv, add_zero]
  | smul s u _ hu => rw [hu, smul_zero]

theorem nontrivial_af : Nontrivial (Formalism.L2.Herm.Af F) := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' := congrArg (fun b : Formalism.L2.Herm.Af F => b v) h
  change (0 : _) = 1 at h'
  exact zero_ne_one h'

theorem mem_smul_span (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (y : Fin n → E)
    (hy : g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    y ∈ 𝔪 • Submodule.span (𝓞 E) {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ} := by
  by_cases h𝔪 : 𝔪 = ⊥
  · subst h𝔪
    have h0 : g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = 0 :=
      eq_zero_of_mem_hatL_bot _ (by simpa [Submodule.bot_smul] using hy)
    have hv : (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = 0 := by
      have := congrArg (fun w => (g⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ w) h0
      simpa [Matrix.mulVec_mulVec] using this
    haveI := nontrivial_af (F := F)
    have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] Formalism.L2.Herm.Af F) :=
      Algebra.TensorProduct.includeLeft_injective (algebraMap F (Formalism.L2.Herm.Af F)).injective
    have hy0 : y = 0 := by
      funext i
      apply hinj
      simpa using congrFun hv i
    subst hy0
    exact Submodule.zero_mem _
  · have hP : (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have h1 : (1 : E) ∈ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
        (((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hP]
      exact FractionalIdeal.one_mem_one _
    have key : ∀ c ∈ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
        (((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E),
        c • y ∈ 𝔪 • Submodule.span (𝓞 E) {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
          Formalism.L2.Herm.hatL (F := F) Λ} := by
      intro c hc
      refine Submodule.mul_induction_on (C := fun c => c • y ∈ 𝔪 • Submodule.span (𝓞 E)
        {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) Λ})
        hc (fun m hm a ha => ?_) (fun u v hu hv => ?_)
      · obtain ⟨m', hm', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
        have hint : ∀ t ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E t * a := by
          intro t ht
          obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
            ((FractionalIdeal.mem_inv_iff hP).1 ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ ht))
          exact ⟨c, by rw [hc, mul_comm]⟩
        have hcol : (fun i => (a • y) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) =
            (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) • (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) := by
          funext i
          show (a * y i) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y i ⊗ₜ[F] 1)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        have haS : g.1 *ᵥ (fun i => (a • y) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
          rw [hcol, Matrix.mulVec_smul]
          exact smul_mem_hatL Λ 𝔪 a hint _ hy
        rw [mul_smul, algebraMap_smul]
        exact Submodule.smul_mem_smul hm' (Submodule.subset_span haS)
      · rw [add_smul]
        exact Submodule.add_mem _ hu hv
    simpa using key 1 h1

end General

theorem mem_smul_latAt : ∀ (D : D7) (V : HSp D) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (x : GA D V) (y : Fin V.rank → D.host.E), (Lev.finE V x⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) → y ∈ 𝔪 • latAt Λ x := by
  intro D V Λ 𝔪 _ x y hy
  unfold GlobalTheory.SepPer.latAt
  exact mem_smul_span Λ 𝔪 (Lev.finE V x⁻¹) y hy

end GlobalTheory.SepLatIdeal

end
end

