module

public import Mathlib
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ColumnStabiliser
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      Subgroup (GL (Fin D.R.k) D.host.E) :=
  letI := D.host.cmStar
  fun y =>
    UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ⊓
      ((Lv u).U.comap (MulAut.conj (y : GL (Fin D.R.k)
          (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))⁻¹).toMonoidHom).comap
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))

theorem mem_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ (y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (γ : GL (Fin D.R.k) D.host.E),
      γ ∈ colStab D Lv u y ↔
        γ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ∧
          (y : GL (Fin D.R.k) _)⁻¹ *
            bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
            (y : GL (Fin D.R.k) _) ∈ (Lv u).U := by
  intro y γ
  simp [colStab, Subgroup.mem_inf, Subgroup.mem_comap]

def ColStabTrivialAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      colStab D Lv u y = ⊥

def ColStabTrivial : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), ColStabTrivialAt D Lv u

theorem map_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (colStab D Lv u y).map (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) =
        ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
          (Lv u).U.map (MulAut.conj (y : GL (Fin D.R.k) _)).toMonoidHom := by
  intro y
  ext x
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_colStab D Lv u y γ).1 hγ
    exact ⟨⟨γ, h1, rfl⟩, ⟨_, h2, by simp [mul_assoc]⟩⟩
  · rintro ⟨⟨γ, h1, rfl⟩, z, hz, hz'⟩
    refine ⟨γ, (mem_colStab D Lv u y γ).2 ⟨h1, ?_⟩, rfl⟩
    rw [← hz']
    simpa [mul_assoc] using hz

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped ENNReal TensorProduct

abbrev RightCosets {G' G : Type} [Group G'] [Group G] (j : G' →* G) : Type :=
  Quotient (QuotientGroup.rightRel j.range)

def IsQuotientMeasure {G' G : Type} [Group G'] [Group G] [MeasurableSpace G'] [MeasurableSpace G]
    (j : G' →* G) (m' : Measure G') (m : Measure G) (ν : Measure (RightCosets j)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂m = ∫⁻ c, ∫⁻ g', f (j g' * Quotient.out c) ∂m' ∂ν

def IsStabEmb {P' Q' P Q : ℕ} (x₀ : Fin P ⊕ Fin Q → ℂ) (j : UpqT P' Q' →* UpqT P Q) : Prop :=
  ∃ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ,
    Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' ∧
    (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x₀ = 0 ∧
    ∀ g' : UpqT P' Q', UpqT.mat (j g') *ᵥ x₀ = x₀ ∧ UpqT.mat (j g') * C = C * UpqT.mat g'

def piEmb {T : Type} {P' Q' P Q : ℕ} (j : T → (UpqT P' Q' →* UpqT P Q)) :
    (T → UpqT P' Q') →* (T → UpqT P Q) where
  toFun g ρ := j ρ (g ρ)
  map_one' := by funext ρ; simp
  map_mul' g h := by funext ρ; simp

def infCoord {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M P Q : ℕ}
    (θ : Ainf F ⊗[F] E →+* ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ)
    (Y : Fin 1 → Fin M → Ainf F ⊗[F] E) : Fin P ⊕ Fin Q → ℂ :=
  A *ᵥ fun i => θ (Y 0 i)

def phiLat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (latHat F E L : Set (Fin M → Af F ⊗[F] E)).indicator 1 (projFin X 0) * Φi (projInf X)

def atInv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) : ℝ≥0∞ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) x)

def coordTup {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) (x : W.V) :
    Fin 1 → Fin W.rank → E :=
  fun _ i => W.frame.repr x i

def UnfoldAt (D : D7) : letI := D.host.cmStar;
    ∀ (W W' : HSpace D.host.E) (_P _Q _P' _Q' : ℕ) (_β : D.host.E) (_x : W.V), Prop :=
  letI := D.host.cmStar
  fun W W' P Q P' Q' β x =>
  ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram))
    (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsVolMeas D W P Q μ → IsVolMeas D W' P' Q' μ' →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
    μ 𝓕 < ⊤ → μ' 𝓕' < ⊤ →
    AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
      ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
    AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
      ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
    AllSome (fun j : D.what₂.Tau → (UpqT P' Q' →* UpqT P Q) =>
      ∀ ρ, IsStabEmb (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) (j ρ)) fun j =>
    AllSome (IsQuotientMeasure (piEmb j) (Measure.pi fun _ => D.cd.cd P' Q')
      (Measure.pi fun _ => D.cd.cd P Q)) fun ν =>
    AllSome (fun pt : (D.what₂.Tau → UpqT P Q) →
        (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
      ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) =
        UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i))) fun pt =>
    ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
      ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = β},
          atInv D.sp.cm.sig W.gram (phiLat (L0c D W) Φi) h (coordTup W x'.1) ∂μ =
        μ' 𝓕' * ∫⁻ c, Φi (pt (Quotient.out c)) ∂ν

def Unfolding (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∀ x : W.V, W.hT x x = (if s then 1 else -1) → x ∈ W.L0 →
    ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
      HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
      (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) →
      (∀ y, y ∈ W'.L0 ↔ ι y ∈ W.L0) →
      UnfoldAt D W W' P Q (if s then P - 1 else P) (if s then Q else Q - 1) (if s then 1 else -1) x

theorem IsStabEmb.inv_mul_fix {P' Q' P Q : ℕ} {x₀ : Fin P ⊕ Fin Q → ℂ} {j : UpqT P' Q' →* UpqT P Q}
    (hj : IsStabEmb x₀ j) (g' : UpqT P' Q') (g : UpqT P Q) :
    UpqT.mat (j g' * g)⁻¹ *ᵥ x₀ = UpqT.mat g⁻¹ *ᵥ x₀ := by
  obtain ⟨C, -, -, h⟩ := hj
  have h1 := (h g'⁻¹).1
  have e : UpqT.mat (j g' * g)⁻¹ = UpqT.mat g⁻¹ * UpqT.mat (j g'⁻¹) := by
    rw [_root_.mul_inv_rev, ← map_inv]; rfl
  rw [e, ← Matrix.mulVec_mulVec, h1]

end GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
section
open MvPolynomial NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

def brOne (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)).toLinearMap ∘ₗ
    (VV K fun _ : Unit => sg).subtype ∘ₗ
      Br.brStdP (K := K) hN (fun _ : Unit => lam) (fun _ : Unit => sg) ∘ₗ
        (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))).toLinearMap

theorem brOne_rename (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : VV K fun _ : Unit => lam) :
    brOne K hN lam sg (rename Prod.snd (G : Pol K Unit N)) =
      rename Prod.snd ((Br.brStd hN (fun _ : Unit => lam) (fun _ : Unit => sg) G : VV K fun _ : Unit => sg) : Pol K Unit n) := by
  have h : rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))
      (rename Prod.snd (G : Pol K Unit N)) = (G : Pol K Unit N) := by
    rw [rename_rename]
    exact rename_id_apply _
  simp only [brOne, Br.brStd, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h, Submodule.subtype_apply]

theorem interlace_iff {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.Interlace hN lam sg ↔ Formalism.MainNotions.PrimeDegreeVariant.Interlace hN.symm lam sg := by
  refine forall_congr' fun i => ?_
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC]
  omega

def OnePlace : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
      Formalism.MainNotions.PrimeDegreeVariant.IsBr hN.symm lam sg (brOne ℂ hN lam sg)

def Equivariance : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → Br.BrEquiv K hN lam sg

def Integrality : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrIntegral K hN lam sg

def Members : Prop :=
  ∀ (X : Fields) (Word : Type) (R : Ranks) (W : Wts X Word R), W.Ok → ∀ (u : Word) (τ : X.Tau),
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) ∧ Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)

def Tensor : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ (f : ι → MvPolynomial (Fin N × Fin N) K) (G : VV K lam), (∀ τ, f τ ∈ nablaSq K N (lam τ)) → (G : Pol K ι N) = ten f →
      ((Br.brStd hN lam sg G : VV K sg) : Pol K ι n) = ten fun τ => brOne K hN (lam τ) (sg τ) (f τ)

theorem members_sameShift {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (hW : W.Ok) (u : Word) (τ : X.Tau) :
    Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ) :=
  (lamTrue_sgTrue_detShift W hW u τ).symm

end GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IsometryTransportFrames
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def HasSig (W : HSpace E) (P Q : ℕ) : Prop := W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def withLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : HSpace E :=
  { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hU }

def frameMat (W₁ W₂ : HSpace E) (e : W₁.V →ₗ[E] W₂.V) : Matrix (Fin W₂.rank) (Fin W₁.rank) E :=
  LinearMap.toMatrix W₁.frame W₂.frame e

def CarriesLat (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop := ∀ x : W₁.V, x ∈ W₁.L0 ↔ e x ∈ W₂.L0

end Spaces

def IsConjBy {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ}
    (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E) (T : Matrix (Fin M₂) (Fin M₁) E)
    (φ : HA (AF F) σ J₁ → HA (AF F) σ J₂) : Prop :=
  ∀ h : HA (AF F) σ J₁,
    ((HA.mat (AF F) σ J₂ (φ h) : GL (Fin M₂) (AF F ⊗[F] E)) : Matrix (Fin M₂) (Fin M₂) (AF F ⊗[F] E)) *
        T.map (inclR (F := F) (AF F)) =
      T.map (inclR (F := F) (AF F)) *
        ((HA.mat (AF F) σ J₁ h : GL (Fin M₁) (AF F ⊗[F] E)) : Matrix (Fin M₁) (Fin M₁) (AF F ⊗[F] E))

def LatticeIndep (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), HasSig W P Q →
    ∀ (L : Submodule (𝓞 D.host.E) W.V) (hL : Submodule.IsLattice D.host.E L)
      (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)),
      IsVolMeas D W P Q μ ↔ IsVolMeas D (withLat W L hL hU) P Q μ

def IsometryTransport (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → CarriesLat W₁ W₂ e →
      ∃ φ : HA (AF D.host.F) D.sp.cm.sig W₁.gram ≃ₜ* HA (AF D.host.F) D.sp.cm.sig W₂.gram,
        IsConjBy D.sp.cm.sig W₁.gram W₂.gram (frameMat W₁ W₂ e.toLinearMap) φ ∧
        (∀ h, h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram ↔
          φ h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) ∧
        (∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
          IsVolMeas D W₁ P Q μ ↔ IsVolMeas D W₂ P Q (μ.map φ)) ∧
        (∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram))
            (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W₁.gram)),
          IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram) 𝓕 μ ↔
            IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) (φ '' 𝓕) (μ.map φ))

def VolEqOfIsometric (D : D7) : Prop :=
  letI := D.host.cmStar
  VolTie D → ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → D.vol W₁ = D.vol W₂

def VolIndep (D : D7) : Prop := LatticeIndep D ∧ IsometryTransport D ∧ VolEqOfIsometric D

end GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal TensorProduct

abbrev RCosets {G G' : Type} [Group G] [Group G'] (j : G' →* G) : Type :=
  Quotient (QuotientGroup.rightRel j.range)

def IsQuotMeasure {G G' : Type} [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G']
    (j : G' →* G) (μ : Measure G) (μ' : Measure G') (ν : Measure (RCosets j)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂μ = ∫⁻ c : RCosets j, ∫⁻ h, f (j h * c.out) ∂μ' ∂ν

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def coords (W : HSpace E) (x : W.V) : Fin 1 → Fin W.rank → E := fun _ i => W.frame.repr x i

end Coord

def latTensor {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (latHat F E L : Set (Fin M → Af F ⊗[F] E)).indicator (fun _ => (1 : ℝ≥0∞)) (projFin X 0) *
    Φi (projInf X)

def atInv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (h : HA (AF F) σ J) (y : Fin 1 → Fin M → E) : ℝ≥0∞ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) y)

def IsInfQuotIntegral (D : D7) : letI := D.host.cmStar; ∀ (W : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_x : W.V) (_Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞)
    (_I : ℝ≥0∞), Prop :=
  letI := D.host.cmStar
  fun W P Q P' Q' x Φi I =>
  AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
    ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
  AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
  let xr : D.what₂.Tau → (Fin P ⊕ Fin Q → ℂ) :=
    fun ρ => A ρ *ᵥ fun i => embOf D ρ (coords W x 0 i)
  AllSome (fun C : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ =>
    ∀ ρ, (C ρ)ᴴ * Formalism.UG.Jpq P Q * C ρ = Formalism.UG.Jpq P' Q' ∧
      ((C ρ)ᴴ * Formalism.UG.Jpq P Q) *ᵥ xr ρ = 0) fun C =>
  AllSome (fun j : (D.what₂.Tau → UpqT P' Q') →* (D.what₂.Tau → UpqT P Q) =>
    ∀ b ρ, UpqT.mat (j b ρ) * C ρ = C ρ * UpqT.mat (b ρ) ∧
      UpqT.mat (j b ρ) *ᵥ xr ρ = xr ρ) fun j =>
  AllSome (fun o : (D.what₂.Tau → UpqT P Q) →
      (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    ∀ g ρ, (A ρ *ᵥ fun i => θ ρ (o g 0 i)) = UpqT.mat (g ρ)⁻¹ *ᵥ xr ρ) fun o =>
  AllSome (IsQuotMeasure j (Measure.pi fun _ => D.cd.cd P Q) (Measure.pi fun _ => D.cd.cd P' Q'))
    fun ν => ∫⁻ c : RCosets j, Φi (o c.out) ∂ν = I

def HidaSetting {E : Type} [Field E] [NumberField E] [StarRing E] (W W' : HSpace E)
    (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[E] W.V) : Prop :=
  W.SigOK ∧ (∀ τ, W.sig τ = (P, Q)) ∧ 3 ≤ W.rank ∧
  (if s then P = P' + 1 ∧ Q = Q' else P = P' ∧ Q = Q' + 1) ∧
  W.hT x x = (if s then 1 else -1) ∧ x ∈ W.L0 ∧
  HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧
  W'.SigOK ∧ (∀ τ, W'.sig τ = (P', Q'))

def UnfoldAt (D : D7) : letI := D.host.cmStar; ∀ (W _W' : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_s : Bool) (_x : W.V), Prop :=
  letI := D.host.cmStar
  fun W W' P Q P' Q' s x =>
  ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsVolMeas D W P Q μ → IsVolMeas D W' P' Q' μ' →
  ∀ (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
    μ 𝓕 < ⊤ → μ' 𝓕' < ⊤ →
  ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
    ∃ I : ℝ≥0∞, IsInfQuotIntegral D W P Q P' Q' x Φi I ∧
      ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)},
        atInv D.sp.cm.sig W.gram (latTensor (L0c D W) Φi) h (coords W x'.1) ∂μ = μ' 𝓕' * I

def Unfolding (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V),
    HidaSetting W W' P Q P' Q' s x ι → (∀ y : W'.V, y ∈ W'.L0 ↔ ι y ∈ W.L0) →
    UnfoldAt D W W' P Q P' Q' s x

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeIndex
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def IsSelfDualLat {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (n → E)) = ⊤ ∧
    (N : Set (n → E)) = dualSet σ J N

def IsSelfDualDefiniteLattice (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N

def stabHat (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  levelAfL D.sp.cm.sig D.sp.gram0 N

def levelU (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  (Lv u).U

def IndexAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  (∀ i : Fin 2, SplitsF D (D.host.g i)) → SplitsF D (D.mem u).A.T →
    ∀ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsSelfDualDefiniteLattice D N →
      levelU D Lv u ≤ stabHat D N →
      (((levelU D Lv u).relIndex (stabHat D N) : ℕ) : ℝ) =
        idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def StabiliserLevelIndexFormula : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), IndexAt D Lv u

theorem factorT_pos (D : D7) (u : D.what₂.Word) :
    0 < (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f := by
  have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
  have hk : D.R.k ≠ 0 := by
    have := D.R.m_add_three_le_k
    omega
  have hTk : (1 : ℝ) < ((D.mem u).A.T : ℝ) ^ D.R.k := one_lt_pow₀ hT hk
  exact pow_pos (by linarith) _

theorem stabHat_le (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    letI := D.host.cmStar
    stabHat D N ≤ UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  intro g hg
  unfold stabHat levelAfL level at hg
  exact (Subgroup.mem_inf.mp hg).1

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

end
end

