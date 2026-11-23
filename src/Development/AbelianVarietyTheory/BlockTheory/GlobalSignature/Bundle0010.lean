module

public import Mathlib
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.OverPlaceIntegralForm
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

def stabRow {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (φ : n → A) :
    Subgroup (GL n A) where
  carrier := {g | φ ᵥ* (g : Matrix n n A) = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : φ ᵥ* (a : Matrix n n A) = φ := ha
    have hb' : φ ᵥ* (b : Matrix n n A) = φ := hb
    show φ ᵥ* ((a * b : GL n A) : Matrix n n A) = φ
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ha', hb']
  inv_mem' := by
    intro g hg
    have hg' : φ ᵥ* (g : Matrix n n A) = φ := hg
    show φ ᵥ* ((g⁻¹ : GL n A) : Matrix n n A) = φ
    conv_lhs => rw [← hg']
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]

section Local

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def toIntV : 𝓞 E →+* intV E v :=
  ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict (intV E v)
    (fun a => Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E a, ⟨a, rfl⟩⟩, rfl⟩))

variable {E} {n : Type}

abbrev latV (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

variable {v}

def pr₁ (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (x : n → E ⊗[F] v.adicCompletion F) : n → v.adicCompletion F := fun i => (s (x i)).1

def pr₂ (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (x : n → E ⊗[F] v.adicCompletion F) : n → v.adicCompletion F := fun i => (s (x i)).2

def IsSplitting (σ : E →ₐ[F] E) (P Pb : HeightOneSpectrum (𝓞 E))
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  P ≠ Pb ∧
  v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * Pb.asIdeal ∧
  (∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
  (∀ x, s (sigR σ (v.adicCompletion F) x) = swapR _ (s x)) ∧
  (∀ x, x ∈ intV E v ↔
    (s x).1 ∈ v.adicCompletionIntegers F ∧ (s x).2 ∈ v.adicCompletionIntegers F) ∧
  (∀ a : 𝓞 E, a ∈ P.asIdeal ↔ Valued.v (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 < 1) ∧
  (∀ a : 𝓞 E, a ∈ Pb.asIdeal ↔ Valued.v (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 < 1)

end Local

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

abbrev baseDual (L : ColLevel R F E sp gp C A clsLat) : Submodule (𝓞 E) (Fin R.k → E) :=
  Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)

def OverAt (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) : Prop :=
  ∃ (P Pb : HeightOneSpectrum (𝓞 E))
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),

    IsSplitting sp.cm.sig P Pb s ∧

    (∀ x : latV v (baseDual L), pr₁ s (x : Fin R.k → _) = 0 → L.fT v hv x = 0) ∧

    (∀ x : latV v (baseDual L),
      L.fT v hv x = 0 ↔ pr₁ s (x : Fin R.k → _) ∈ pr₁ s '' (latV v L.Lb : Set (Fin R.k → _))) ∧

    Nonempty ((latV v (baseDual L) ⧸ (latV v L.Lb).submoduleOf (latV v (baseDual L))) ≃ₗ[intV E v]
      ((intV E v ⧸ P.asIdeal.map (toIntV E v)) × (intV E v ⧸ Pb.asIdeal.map (toIntV E v)))) ∧

    pr₁ s '' (latV v N : Set (Fin R.k → _)) = pr₁ s '' (latV v (baseDual L) : Set (Fin R.k → _)) ∧
    pr₂ s '' (latV v N : Set (Fin R.k → _)) = pr₂ s '' (latV v L.Lb : Set (Fin R.k → _)) ∧

    (∃ hle : latV v N ≤ latV v (baseDual L),
      (L.fT v hv).comp (Submodule.inclusion hle) ≠ 0 ∧
      L.Uloc v = levelVL sp.cm.sig sp.gram0 v N ⊓
        stabFun (latV v N) ((L.fT v hv).comp (Submodule.inclusion hle))) ∧

    ∃ (h : GL (Fin R.k) (v.adicCompletion F))
      (φ : Fin R.k → v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
      (e : L.fM v hv ≃+
        v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)),
      pr₁ s '' (latV v N : Set (Fin R.k → _)) =
        Set.range (fun y : Fin R.k → v.adicCompletionIntegers F =>
          (h : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ fun i => (y i : v.adicCompletion F)) ∧
      Set.BijOn (fun g : GL (Fin R.k) (E ⊗[F] v.adicCompletion F) =>
          h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) g * h)
        (levelVL sp.cm.sig sp.gram0 v N)
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range ∧
      φ ≠ 0 ∧
      (∀ (x : latV v (baseDual L)) (y : Fin R.k → v.adicCompletionIntegers F),
        pr₁ s (x : Fin R.k → _) =
          (h : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ (fun i => (y i : v.adicCompletion F)) →
        e (L.fT v hv x) = ∑ i, φ i * Ideal.Quotient.mk _ (y i)) ∧
      ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
        g ∈ L.Uloc v ↔ h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) g * h ∈
          congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (stabRow φ)

def IsOverLattice (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧
  Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E)) ∧
  L.Lb ≤ N ∧
  (N : Set (Fin R.k → E)) ⊆ dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb ∧
  (∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → latV v N = latV v L.Lb) ∧
  (∀ (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal), OverAt L N v hv) ∧
  L.U ≤ levelAfL sp.cm.sig sp.gram0 N

end Level

def OverLatticeAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T →
    (∀ i : Fin 2, (D.mem u).A.T ≠ D.host.g i) ∧
    ∃ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsOverLattice (Lv u) N

def OverLattice : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), OverLatticeAt D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualStabiliserIndex
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice

def IsSelfDualLat {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (n → E)) = ⊤ ∧
    dualSet σ J N = (N : Set (n → E))

def stabK (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    Subgroup (GL (Fin D.R.k)
      (TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :=
  letI := D.host.cmStar
  levelAfL D.sp.cm.sig D.sp.gram0 N

def IndexAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  (∀ i : Fin 2, SplitsF D (D.host.g i)) → SplitsF D (D.mem u).A.T →
    ∀ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E),
      IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N →
      (Lv u).U ≤ stabK D N →
      (((Lv u).U.relIndex (stabK D N) : ℕ) : ℝ) =
        idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def IndexKU : Prop := ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), IndexAt D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignatureLatticeIndependence
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def withLattice (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : HSpace E :=
  { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hU }

def HasSignatureEverywhere (W : HSpace E) (P Q : ℕ) : Prop :=
  W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def IsIsometry (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop :=
  HSpace.IsIsomEmb W₁ W₂ e.toLinearMap

def CarriesLattice (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop :=
  ∀ x : W₁.V, x ∈ W₁.L0 ↔ e x ∈ W₂.L0

def frameMatrix (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Matrix (Fin W₂.rank) (Fin W₁.rank) E :=
  LinearMap.toMatrix W₁.frame W₂.frame e.toLinearMap

end Spaces

def Intertwines {A : Type} [CommRing A] {M₁ M₂ : ℕ} (C : Matrix (Fin M₂) (Fin M₁) A)
    (g₁ : Matrix (Fin M₁) (Fin M₁) A) (g₂ : Matrix (Fin M₂) (Fin M₂) A) : Prop :=
  g₂ * C = C * g₁

def pointMatrix {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  (HA.mat R σ J h).val

def baseChange {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {M₁ M₂ : ℕ} (C : Matrix (Fin M₂) (Fin M₁) E) : Matrix (Fin M₂) (Fin M₁) (R ⊗[F] E) :=
  C.map (inclR R)

def IsConjugationBy {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M₁ M₂ : ℕ} (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E)
    (C : Matrix (Fin M₂) (Fin M₁) E) (Φ : HA R σ J₁ → HA R σ J₂) : Prop :=
  ∀ h : HA R σ J₁, Intertwines (baseChange R C) (pointMatrix R σ J₁ h) (pointMatrix R σ J₂ (Φ h))

def LatticeIndependence (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W P Q →
    ∀ (L L' : Submodule (𝓞 D.host.E) W.V)
      (hL : Submodule.IsLattice D.host.E L) (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L)
      (hL' : Submodule.IsLattice D.host.E L') (hU' : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L')
      (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)),
      IsVolMeas D (withLattice W L hL hU) P Q μ ↔ IsVolMeas D (withLattice W L' hL' hU') P Q μ

def IsometryTransport (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W₁ P Q → HasSignatureEverywhere W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, IsIsometry W₁ W₂ e → CarriesLattice W₁ W₂ e →
      ∃ Φ : HA (AF D.host.F) D.sp.cm.sig W₁.gram ≃ₜ* HA (AF D.host.F) D.sp.cm.sig W₂.gram,
        IsConjugationBy (AF D.host.F) D.sp.cm.sig W₁.gram W₂.gram (frameMatrix W₁ W₂ e) Φ ∧
        (∀ h : HA (AF D.host.F) D.sp.cm.sig W₁.gram,
          HA.mat (AF D.host.F) D.sp.cm.sig W₁.gram h ∈ HFin (AF D.host.F) D.sp.cm.sig W₁.gram ↔
            HA.mat (AF D.host.F) D.sp.cm.sig W₂.gram (Φ h) ∈ HFin (AF D.host.F) D.sp.cm.sig W₂.gram) ∧
        (∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
          IsVolMeas D W₁ P Q μ ↔ IsVolMeas D W₂ P Q (μ.map Φ)) ∧
        ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram), IsVolMeas D W₁ P Q μ →
          ∀ 𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
            IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram) 𝓕 μ ↔
              IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) (Φ '' 𝓕) (μ.map Φ)

def VolumeInvariance (D : D7) : Prop :=
  letI := D.host.cmStar
  VolTie D →
    ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSignatureEverywhere W₁ P Q → HasSignatureEverywhere W₂ P Q →
      (∃ e : W₁.V ≃ₗ[D.host.E] W₂.V, IsIsometry W₁ W₂ e) → D.vol W₁ = D.vol W₂

def VolumeIndependence (D : D7) : Prop :=
  LatticeIndependence D ∧ IsometryTransport D ∧ VolumeInvariance D

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsSplitting (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  (∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
  (∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)) ∧
  (∀ x, x ∈ intV E v ↔
    (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F)

variable {v : HeightOneSpectrum (𝓞 F)}
  (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

def prP : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom

def prPbar : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.snd _ _).comp φ.toRingHom

def primeOf (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) : Ideal (intV E v) :=
  Ideal.span {a : intV E v | Valued.v (p a) < 1}

def partOf {n : Type} (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (Λ : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F)) :
    Submodule (v.adicCompletionIntegers F) (n → v.adicCompletion F) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : n → E ⊗[F] v.adicCompletion F => fun i => p (x i)) '' (Λ : Set _))

abbrev locLat {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (n → E)) : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

end Local

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

abbrev dualLb (L : ColLevel R F E sp gp C A clsLat) : Submodule (𝓞 E) (Fin R.k → E) :=
  Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)

def IsOverLattice (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E)) ∧
  L.Lb ≤ N ∧ N ≤ dualLb L ∧
  ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → locLat v N = locLat v L.Lb

def LocalAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal)
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=

  IsSplitting sp.cm.sig v φ ∧

  (∀ x : locLat v (dualLb L), (∀ i, prP φ (x.1 i) = 0) → L.fT v h x = 0) ∧

  Nonempty ((locLat v (dualLb L) ⧸ (locLat v L.Lb).submoduleOf (locLat v (dualLb L))) ≃ₗ[intV E v]
    (intV E v ⧸ primeOf (prP φ)) × (intV E v ⧸ primeOf (prPbar φ))) ∧

  partOf (prP φ) (locLat v N) = partOf (prP φ) (locLat v (dualLb L)) ∧
  partOf (prPbar φ) (locLat v N) = partOf (prPbar φ) (locLat v L.Lb) ∧

  (∀ g' : GL (Fin R.k) (v.adicCompletion F),
    ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (prP φ) g.1 = g') ∧

  (∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
    g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ bc (prP φ) g ∈ stabGL (partOf (prP φ) (locLat v N))) ∧

  (∃ b : GL (Fin R.k) (v.adicCompletion F),
    (∀ y : Fin R.k → v.adicCompletion F,
      (b : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ y ∈ partOf (prP φ) (locLat v N) ↔
        ∀ i, y i ∈ v.adicCompletionIntegers F) ∧
    ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (prP φ) g * b ∈
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range) ∧

  ∃ (f : partOf (prP φ) (locLat v N) →ₗ[v.adicCompletionIntegers F]
      IsLocalRing.ResidueField (v.adicCompletionIntegers F))
    (ε : L.fM v h ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F)),
    (∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP φ a →
      ∀ m, ε (a • m) = a' • ε m) ∧
    (∀ (x : locLat v (dualLb L)) (y : partOf (prP φ) (locLat v N)),
      (∀ i, y.1 i = prP φ (x.1 i)) → f y = ε (L.fT v h x)) ∧
    f ≠ 0 ∧
    (∀ y, f ((A.T : v.adicCompletionIntegers F) • y) = 0) ∧
    (∀ y, f y = 0 ↔ y.1 ∈ partOf (prP φ) (locLat v L.Lb)) ∧
    ∀ g, g ∈ L.Uloc v ↔
      g ∈ levelVL sp.cm.sig sp.gram0 v N ∧ bc (prP φ) g ∈ stabFun (partOf (prP φ) (locLat v N)) f

def HasOverLattice (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  (∀ i : Fin 2, A.T ≠ gp i) ∧
  ∃ N : Submodule (𝓞 E) (Fin R.k → E), IsOverLattice L N ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal), ∃ φ, LocalAtT L N v h φ) ∧
    (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
    L.U ≤ levelAfL sp.cm.sig sp.gram0 N

end Level

def SelfDualOverBase : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    letI := D.host.cmStar
    Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → HasOverLattice (Lv u)

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers

open scoped TensorProduct Pointwise
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

section Lat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def IsSelfDualLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin M → E)) = ⊤ ∧
    ∀ y : Fin M → E, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (hE σ J x y)

def perpIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) : Set (Fin M → E) :=
  {y | y ∈ L ∧ hE σ J x y = 0}

variable (R : Type) [CommRing R] [Algebra F R]

def actV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : Fin M → R ⊗[F] E :=
  (h • (fun _ => y : Fin 1 → Fin M → R ⊗[F] E)) 0

theorem actV_eq (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) :
    actV R σ J h y = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec y := rfl

theorem actV_one (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (y : Fin M → R ⊗[F] E) : actV R σ J 1 y = y := by
  unfold actV
  rw [one_smul]

theorem actV_mul (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : actV R σ J (g * h) y = actV R σ J g (actV R σ J h y) := by
  unfold actV
  rw [mul_smul]
  rfl

def stabLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Λ : AddSubgroup (Fin M → R ⊗[F] E)) : Subgroup (HA R σ J) where
  carrier := {h | ∀ y, y ∈ Λ ↔ actV R σ J h y ∈ Λ}
  one_mem' := by intro y; rw [actV_one]
  mul_mem' := by
    intro a b ha hb y
    rw [actV_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (actV R σ J g⁻¹ y)
    rw [← actV_mul, mul_inv_cancel, actV_one] at this
    exact this.symm

end Lat

def UnramifiedAtFinite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop :=
  ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 F) P

def OrbitConcl (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) : Prop :=
  (∀ y ∈ latHat F E (L : Set (Fin M → E)), qR (Af F) σ J y = algebraMap F (Af F) β →
      ∃ k ∈ stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))),
        actV (Af F) σ J k (fun i => inclR (F := F) (Af F) (x i)) = y) ∧
  ({h : HA (Af F) σ J | actV (Af F) σ J h⁻¹ (fun i => inclR (F := F) (Af F) (x i)) ∈
        latHat F E (L : Set (Fin M → E))} =
      (Hstab (Af F) σ J (fun _ => x) : Set (HA (Af F) σ J)) *
        (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) : Set (HA (Af F) σ J))) ∧
  (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) ⊓ Hstab (Af F) σ J (fun _ => x) =
      stabLat (Af F) σ J (latHat F E (perpIn σ J L x)) ⊓ Hstab (Af F) σ J (fun _ => x))

def StabTransitive : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L →
    ∀ β : F, (β = 1 ∨ β = -1) →
    ∀ x ∈ L, hE σ J x x = algebraMap F E β → OrbitConcl F E σ J L x β

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers
end
end

