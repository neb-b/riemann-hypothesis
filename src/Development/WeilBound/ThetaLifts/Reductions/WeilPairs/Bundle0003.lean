module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0002
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.EtaDef
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0219
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsAlt
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev tauB (B : Base F E) : InfinitePlace F → (E →+* ℂ) := fun w => (B.emb w).1

structure Ctx (σ : E →ₐ[F] E) (B : Base F E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E) : Prop where
  good : B.IsGood σ
  hS : IsHermND σ JS
  hT : IsHermND σ JT
  h0 : ξ₀ ≠ 0
  hξ : σ ξ₀ = -ξ₀
  inf : IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ
  chart : IsChartF θ ι


variable (F E) in
def finIdem : AEF F E := algebraMap (AF F) (AEF F E) (pairA F 0 1)

theorem infPartF_finIdem : infPartF F E (finIdem F E) = 0 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 1 ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem finIdem_smul_fin {nS nT : ℕ} (x : WOF F E nS nT) : (finIdem F E • x).map (infPartF F E) = 0 := by
  funext i j
  show infPartF F E (finIdem F E * x i j) = 0
  rw [map_mul, infPartF_finIdem, zero_mul]


variable (F) in
def finRatF {nS nT : ℕ} : Matrix (Fin nT) (Fin nS) E →ₗ[𝓞 E] XFF F E nS nT where
  toFun y := XFF.mk (finIdem F E • ratWF (F := F) y) (finIdem_smul_fin _)
  map_add' x y := XFF.ext (by
    show finIdem F E • ratWF (F := F) (x + y) = finIdem F E • ratWF (F := F) x + finIdem F E • ratWF (F := F) y
    rw [← smul_add]
    congr 1
    funext i j
    exact (incAF F E).map_add (x i j) (y i j))
  map_smul' r x := XFF.ext (by
    show finIdem F E • ratWF (F := F) (r • x) = intAF F r • finIdem F E • ratWF (F := F) x
    rw [smul_comm]
    congr 1
    funext i j
    exact (incAF F E).map_mul (r : E) (x i j))

def infRatF {nS nT : ℕ} (τ : InfinitePlace F → (E →+* ℂ)) : Matrix (Fin nT) (Fin nS) E →+ (IxF F nS nT → ℂ) where
  toFun y := fun p => τ p.2 (y p.1.1 p.1.2)
  map_zero' := funext fun p => (τ p.2).map_zero
  map_add' x y := funext fun p => (τ p.2).map_add _ _

def piWA {nS nT : ℕ} (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) : WOF F E nS nT →+ (IxF F nS nT → ℂ) where
  toFun := piWF θ
  map_zero' := funext fun p => by simp [piWF]
  map_add' x y := funext fun p => by simp [piWF]

def iotaA {nS nT : ℕ} (ι : (InfinitePlace F → ℂ) →+ AEF F E) : (IxF F nS nT → ℂ) →+ WOF F E nS nT where
  toFun := iotaVF ι
  map_zero' := iotaVF_zero ι
  map_add' := iotaVF_add ι

section Lin

variable {κ : Type} [Fintype κ]

def omV (H : Matrix κ κ ℂ) : (κ → ℂ) →ₗ[ℝ] (κ → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => -(star y ⬝ᵥ H *ᵥ x).im)
    (fun x x' y => by rw [mulVec_add, dotProduct_add, Complex.add_im]; ring)
    (fun c x y => by rw [mulVec_smul, dotProduct_smul, Complex.smul_im, smul_eq_mul, smul_eq_mul]; ring)
    (fun x y y' => by rw [star_add, add_dotProduct, Complex.add_im]; ring)
    (fun c x y => by rw [star_smul, star_trivial, smul_dotProduct, Complex.smul_im, smul_eq_mul, smul_eq_mul]; ring)

theorem omV_apply (H : Matrix κ κ ℂ) (x y : κ → ℂ) : omV H x y = -(star y ⬝ᵥ H *ᵥ x).im := rfl

def jV (s : Matrix κ κ ℂ) : (κ → ℂ) →ₗ[ℝ] (κ → ℂ) where
  toFun v := Complex.I • s *ᵥ v
  map_add' x y := by rw [mulVec_add, smul_add]
  map_smul' c x := by rw [mulVec_smul, smul_comm]; rfl

theorem jV_apply (s : Matrix κ κ ℂ) (v : κ → ℂ) : jV s v = Complex.I • s *ᵥ v := rfl

def gaussV (H s g : Matrix κ κ ℂ) (v : κ → ℂ) : ℂ :=
  Complex.exp (-(Real.pi * Complex.I) * (omV H (g *ᵥ v) v : ℝ)) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omV H (g *ᵥ v - v) (jV s (g *ᵥ v - v)) : ℝ))

end Lin

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)

def IsRatF {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (a : Matrix (Fin n) (Fin n) E) : Prop :=
  mtF σ J g = a.map (incAF F E)

def gamQF (ψ : AddChar (AF F) ℂ) (x y : Matrix (Fin nT) (Fin nS) E) : ℂ :=
  gamFF σ JS JT ξ₀ ψ (finRatF F x) (finRatF F y)

structure CartF (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ))
    (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ) : Prop where
  sq : s * s = 1
  pos : (HMF JS JT ξ₀ (tauB B) * s).PosDef
  cen : ∀ (k : GAF σ JT) (t : E), IsRatF σ JT k (t • 1) → s * mMF σ JS JT θ (1, k) = mMF σ JS JT θ (1, k) * s

def IsVacF (ψ : AddChar (AF F) ℂ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ)
    (f : WOF F E nS nT → ℂ) : Prop :=
  ∀ x z, deriv (fun t : ℝ => heisOF σ JS JT ξ₀ ψ (iotaVF ι (t • z)) f x) 0 +
    Complex.I * deriv (fun t : ℝ => heisOF σ JS JT ξ₀ ψ (iotaVF ι (t • jV s z)) f x) 0 = 0

def chiLatF (ψ : AddChar (AF F) ℂ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E) (x : WOF F E nS nT) : ℂ :=
  if finIdem F E • x ∈ latOF F E nS nT Λ then
    ψ (symplOHF σ JS JT ξ₀ (intAF F w • finIdem F E • x) (finIdem F E • x)) else 0

def serF (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E)
    (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (a : IxF F nS nT → ℂ) : WOF F E nS nT → ℂ :=
  GlobalTheory.HeisenbergGaussianSeries.series (G := WOF F E nS nT) (piWA θ) (iotaA ι) (fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y))
    (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT) (chiLatF σ JS JT ξ₀ B.ψ Λ w) a

def zF (η : (AEF F E)ˣ →* Circle) (ε : AEF F E) (h : ε * ε = ε) (p : GAF σ JS × GAF σ JT) : Circle :=
  ((η ^ nT) (GlobalTheory.SplitDetCharF.cutDet σ JS ε h p.1))⁻¹ * (η ^ nS) (GlobalTheory.SplitDetCharF.cutDet σ JT ε h p.2)

structure IsHalfF (ε : AEF F E) : Prop where
  idem : ε * ε = ε
  orth : ε * cAF σ ε = 0
  fin : infPartF F E ε = 0
  split : ∀ e, IsSplitIdemF σ e → (ε * e = e ∧ ε * cAF σ e = 0) ∨ (ε * e = 0 ∧ ε * cAF σ e = cAF σ e)

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.ModulusDerivativeNormalisation

open PositivityTheory.ThKW.ModulusFactorDefinition

def dCdE {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + n)) (Fin n) E :=
  (Matrix.fromRows ((1 / 2 : E) • J⁻¹) (-((1 / 2 : E) • J⁻¹))).submatrix finSumFinEquiv.symm id

def dCd (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + n)) (Fin n) (AF F ⊗[F] E) :=
  (dCdE J).map (incAF F E)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def phase (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (y v : WOF F E nS nT) : ℂ :=
  ψ (symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dCd F JT * v) (dC (AF F ⊗[F] E) nT * y))

def nrm (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (f : WOF F E nS (nT + nT) → ℂ) (v : WOF F E nS nT) : ℂ :=
  GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
               (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ (dCd F JT * v) f) *
    starRingEnd ℂ (GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
      (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ (dCd F JT * v) f))

end PositivityTheory.ThKW.ModulusDerivativeNormalisation

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatH
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def LatH (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) : Prop :=
  ∃ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ ∧ RatSD σ JS JT ξ₀ Λ

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB_A
section
noncomputable section

open scoped TensorProduct Matrix Topology nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_trace_one (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) : ∃ b : 𝓞 E, Algebra.trace F E (b : E) = 1 := by
  classical
  haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have htop : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra hn
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hn
    exact (not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).2 inferInstance (Ideal.dvd_iff_le.2 hle)
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have e := coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)
    rw [htop, FractionalIdeal.coeIdeal_top] at e
    exact inv_eq_one.mp e.symm
  let J : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  by_cases hJ : J = ⊤
  · have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := h1
    refine ⟨b, ?_⟩
    have := Algebra.algebraMap_intTrace (K := F) (L := E) (A := 𝓞 F) b
    rw [hb, map_one] at this
    exact this.symm
  · exfalso
    obtain ⟨p, hp, hJp⟩ := Ideal.exists_le_maximal J hJ
    have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)
    obtain ⟨t, ht, ht1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hp0 hp.ne_top
    have hmem : algebraMap F E t ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (by simp)]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      have hb : Algebra.intTrace (𝓞 F) (𝓞 E) b ∈ p := hJp ⟨b, rfl⟩
      have hp0' : (p : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
      have h2 : t * algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) b) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        have := FractionalIdeal.mul_mem_mul ht ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hb, rfl⟩)
        rwa [inv_mul_cancel₀ hp0'] at this
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h2
      refine ⟨c, ?_⟩
      rw [hc, Algebra.traceForm_apply, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul,
        Algebra.algebraMap_intTrace (L := E)]
    rw [hd] at hmem
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
    have hint : IsIntegral ℤ t := by
      rw [← isIntegral_algebraMap_iff (B := E), ← hc]
      exact RingOfIntegers.isIntegral_coe c
    exact ht1 ((FractionalIdeal.mem_one_iff _).2 ⟨⟨t, hint⟩, rfl⟩)

theorem exists_w (h : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) : ∃ w : 𝓞 E, w + sgOF σ w = 1 := by
  obtain ⟨b, hb⟩ := exists_trace_one hu
  refine ⟨b, RingOfIntegers.ext ?_⟩
  show (b : E) + σ b = 1
  rw [← PositivityTheory.ThKG.Tow.Pln.trace_cm h, hb, map_one]

theorem sg_comm (h : IsCMExt F E σ) (g : E ≃ₐ[ℚ] E) (x : E) : g (σ x) = σ (g x) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  have h1 := h.2.2.2 (τ.comp (g : E →+* E)) x
  have h2 := h.2.2.2 τ (g x)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at h1
  rw [h2]
  exact h1

theorem sg_sg (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sg_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  have := h.2.1
  by_contra hn
  push Not at hn
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hn y] at this
  simpa using this.symm

theorem inertQ_of_fix (h : IsCMExt F E σ) [IsGalois ℚ E] {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 E) ∈ P) (hfix : ∀ r ∈ P, sgOF σ r ∈ P) : InertQF σ q := by
  intro Q hQ hqQ r hr
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → P.LiesOver (Ideal.span {(q : ℤ)}) :=
    fun P hP h => ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
      simpa using h)⟩
  haveI := key P hP.isPrime hqP
  haveI := key Q hQ.isPrime hqQ
  obtain ⟨g, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hr ⊢
  have e : g⁻¹ • sgOF σ r = sgOF σ (g⁻¹ • r) := RingOfIntegers.ext (sg_comm h g⁻¹ r)
  rw [e]
  exact hfix _ hr

theorem exists_move (h : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) {P : Ideal (𝓞 E)}
    (hP : P.IsMaximal) : ∃ r, sgOF σ r - r ∉ P := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have hσ := sg_sg h
  haveI : P.IsMaximal := hP
  have : (P.under (𝓞 F)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) (P.under (𝓞 F)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcard
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => by
    obtain ⟨x, hx⟩ := sg_ne h
    exact hx (congrArg (fun t : E ≃ₐ[F] E => t x) hs)
  by_contra hn
  push Not at hn
  have hs : s ∈ P.inertia (E ≃ₐ[F] E) := AddSubgroup.mem_inertia.2 fun x => hn x
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact hs1 hs

theorem exists_goodNorm (h : IsCMExt F E σ) [IsGalois ℚ E] (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) :
    ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam ∧
      ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  classical
  obtain ⟨lam, h0, h1, h2⟩ := GlobalTheory.FinWeil.exists_lam (InertQF σ)
    fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E)
  refine ⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩
  obtain ⟨q, hq, hqP, hf, hc⟩ := GlobalTheory.FinWeil.exists_card_eq_pow P hP
  have hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  refine ⟨?_, fun hfix => ⟨?_, exists_move h hu hP⟩⟩
  · rw [hc]
    by_cases hI : InertQF σ q
    · rw [h1 q hq hf hI, neg_sq, hsq]
    · rw [h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI
        ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]
  · rw [hc]
    exact h1 q hq hf (inertQ_of_fix h hP hq hqP hfix)

end PositivityTheory.ThKW.LatB

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def dC (n : ℕ) : Matrix (Fin (n + n)) (Fin n) (AF F ⊗[F] E) :=
  ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)


variable (F E) in
def aC (n : ℕ) : Matrix (Fin (n + n)) (Fin n) (AF F ⊗[F] E) :=
  ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (-1)).submatrix finSumFinEquiv.symm id)

def prof (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (f : WOF F E nS (nT + nT) → ℂ) (y : WOF F E nS nT) : ℂ :=
  GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT)
    (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ (aC F E nT * y) f)

end GlobalTheory.SplitLagrF

end
end

