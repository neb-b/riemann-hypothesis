module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.MirabolicMackeyTheory.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Divisibility.Frames
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues

section OnePlace

variable {n d : ℕ}

def metOf (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (Y⁻¹)ᴴ * Y⁻¹

def frameOf (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (CFC.sqrt A)⁻¹

def quotMetC (P : Matrix (Fin d) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (P * A⁻¹ * Pᴴ)⁻¹

def restrMetC (C : Matrix (Fin n) (Fin d) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Cᴴ * A * C

end OnePlace

section AllPlaces

variable {K : Type} [Field K] [NumberField K] {n d D : ℕ}

def stdFrame (H : Matrix (Fin n) (Fin n) K) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => frameOf (H.map v.embedding)

def quotFrame (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K) :
    InfinitePlace K → Matrix (Fin D) (Fin D) ℂ :=
  fun v => frameOf (quotMetC (P.map v.embedding) (H.map v.embedding))

def restrFrame (E : Matrix (Fin n) (Fin d) K) (H : Matrix (Fin n) (Fin n) K) :
    InfinitePlace K → Matrix (Fin d) (Fin d) ℂ :=
  fun v => frameOf (restrMetC (E.map v.embedding) (H.map v.embedding))

def weightMet {Ix : Type} [Fintype Ix] (pr : Ix → Matrix (Fin n) (Fin n) K)
    (t : Ix → InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p, ((t p v : ℝ) : ℂ) • restrMetC ((pr p).map v.embedding) (metOf (X v))

def weightFrame {Ix : Type} [Fintype Ix] (pr : Ix → Matrix (Fin n) (Fin n) K)
    (t : Ix → InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => frameOf (weightMet pr t X v)

def pushFrame (φ : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => φ.map v.embedding * X v


open Classical in
def spliceFrame (v0 : InfinitePlace K) (Y : Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  Function.update X v0 Y

def rowFrame {Ix : Type} [Fintype Ix] (v0 : InfinitePlace K) (Y : Matrix (Fin n) (Fin n) ℂ)
    (φ : Matrix (Fin n) (Fin n) K) (pr : Ix → Matrix (Fin n) (Fin n) K)
    (t : Ix → InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  spliceFrame v0 Y (pushFrame φ (weightFrame pr t X))

def toHLat [StarRing K] (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (L : Submodule (𝓞 K) (Fin d → K)) : Formalism.BasicNotions.HLat K where
  V := Fin d → K
  ι := Fin d
  b := Pi.basisFun K (Fin d)
  X := X
  L := L

end AllPlaces

def FrameOfSpec : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    IsUnit (frameOf A).det ∧ metOf (frameOf A) = A

def MetOfSpec : Prop :=
  ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), IsUnit Y.det →
    (metOf Y).PosDef ∧ (metOf Y)⁻¹ = Y * Yᴴ ∧ metOf (frameOf (metOf Y)) = metOf Y

def QuotRestrPosDef : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    (∀ P : Matrix (Fin d) (Fin n) ℂ, Function.Surjective P.mulVec → (quotMetC P A).PosDef) ∧
    (∀ C : Matrix (Fin n) (Fin d) ℂ, Function.Injective C.mulVec → (restrMetC C A).PosDef)

def QuotEqRestrC : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    ∀ (C : Matrix (Fin n) (Fin d) ℂ) (P : Matrix (Fin d) (Fin n) ℂ), P * C = 1 →
      Cᴴ * A * (1 - C * P) = 0 → quotMetC P A = restrMetC C A

def StdFrameHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v0 : InfinitePlace K) (n : ℕ)
    (H : Matrix (Fin n) (Fin n) K),
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) → IsHermAt v0 H (stdFrame H)

def QuotFrameIsQuot : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D : ℕ) (H : Matrix (Fin n) (Fin n) K),
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec → IsQuotMetric P H (quotFrame P H)

def RestrFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
    ∀ v : InfinitePlace K, IsUnit (restrFrame E H v).det ∧
      metOf (restrFrame E H v) = restrMetC (E.map v.embedding) (H.map v.embedding) ∧
      ∀ x y : Fin d → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) (restrFrame E H) v x y =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (stdFrame H) v (E.mulVec x) (E.mulVec y)

def RestrFrameHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
      IsHermAt v0 (Eᴴ * H * E) (restrFrame E H)

def RestrFrameRatHerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    (∀ a ∈ K0, star a ∈ K0) →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec → (∀ i a, E i a ∈ K0) →
      IsRatHerm K0 (Eᴴ * H * E) (restrFrame E H) ∧ restrFrame E H = stdFrame (Eᴴ * H * E)

def QuotEqRestrAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (H.map v0.embedding).PosDef →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      quotFrame Pr H v0 = restrFrame E H v0

def QuotEqRestrRat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), (∀ i a, E i a ∈ K0) →
      IsOrthProj H E Pr → quotFrame Pr H = restrFrame E H

def QuotFrameHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      IsHermAt v0 (Eᴴ * H * E) (quotFrame Pr H)

def WeightFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (Ix : Type) [Fintype Ix]
    (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
    (∀ p v, 0 < t p v) → ∑ p, pr p = 1 →
    ∀ v : InfinitePlace K, IsUnit (weightFrame pr t X v).det ∧
      metOf (weightFrame pr t X v) = weightMet pr t X v ∧
      ∀ x y : Fin n → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (weightFrame pr t X) v x y =
        ∑ p, ((t p v : ℝ) : ℂ) *
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v ((pr p).mulVec x) ((pr p).mulVec y)

def WeightFramePart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (Ix : Type) [Fintype Ix]
    (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
    (∀ p v, 0 < t p v) → ∑ p, pr p = 1 → (∀ p q, p ≠ q → pr p * pr q = 0) →
    ∀ v : InfinitePlace K,
    (∀ p q, p ≠ q → ∀ x y : Fin n → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v ((pr p).mulVec x) ((pr q).mulVec y) = 0) →
    ∀ (p : Ix) (x y : Fin n → K), (pr p).mulVec x = x →
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (weightFrame pr t X) v x y =
        ((t p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y

def SpliceFrameSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v0 : InfinitePlace K)
    (Y : Matrix (Fin n) (Fin n) ℂ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    spliceFrame v0 Y X v0 = Y ∧ ∀ v, v ≠ v0 → spliceFrame v0 Y X v = X v

end Formalism.L2.DIV
end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.Tuples
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

namespace Formalism.L2.DIV

def kills {G : Type} (A : Type) [Group G] [CommGroup A] (H : Subgroup G) : Subgroup (G →* A) where
  carrier := {ξ | H ≤ ξ.ker}
  one_mem' := fun x _ => by simp
  mul_mem' := fun {a b} ha hb x hx => by
    have h1 := ha hx
    have h2 := hb hx
    rw [MonoidHom.mem_ker] at h1 h2 ⊢
    rw [MonoidHom.mul_apply, h1, h2, one_mul]
  inv_mem' := fun {a} ha x hx => by
    have h1 := ha hx
    rw [MonoidHom.mem_ker] at h1 ⊢
    rw [MonoidHom.inv_apply, h1, inv_one]

theorem mem_kills {G A : Type} [Group G] [CommGroup A] {H : Subgroup G} {ξ : G →* A} :
    ξ ∈ kills A H ↔ H ≤ ξ.ker := Iff.rfl

section Ideles

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev AfE : Type := E ⊗[F] FiniteAdeleRing (𝓞 F) F

abbrev RInt : Subring (AfE F E) := tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

def ratId : Eˣ →* (AfE F E)ˣ := Units.map (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

def idF : (FiniteAdeleRing (𝓞 F) F)ˣ →* (AfE F E)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : FiniteAdeleRing (𝓞 F) F →ₐ[F] AfE F E).toRingHom.toMonoidHom

def intU : Subgroup (AfE F E)ˣ := (RInt F E).toSubmonoid.units

def congU (I : Ideal (RInt F E)) : Subgroup (AfE F E)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker.map (Units.map (RInt F E).subtype.toMonoidHom)

def congN (N : ℕ) : Subgroup (AfE F E)ˣ := congU F E (Ideal.span {(N : RInt F E)})

variable {F}

def suppAt (v : HeightOneSpectrum (𝓞 F)) : Subgroup (AfE F E)ˣ :=
  ⨅ (v' : HeightOneSpectrum (𝓞 F)) (_ : v' ≠ v), (Units.map (prV (E := E) v').toMonoidHom).ker

def inertAt (v : HeightOneSpectrum (𝓞 F)) : Subgroup (AfE F E)ˣ := intU F E ⊓ suppAt E v

def wildAt (v : HeightOneSpectrum (𝓞 F)) : Subgroup (AfE F E)ˣ :=
  congU F E (Ideal.span {((plc v : ℕ) : RInt F E)}).radical ⊓ suppAt E v

def SplitAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ P P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal


variable {E} in
def DegOne (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (Ideal.absNorm v.asIdeal).Prime ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∉ v.asIdeal ^ 2

def GoodPl (S : Set ℕ) (v : HeightOneSpectrum (𝓞 F)) : Prop := SplitAt E v ∧ DegOne v ∧ plc v ∉ S

end Ideles

theorem mem_kerRed {R : Type} [CommRing R] (I : Ideal R) (u : Rˣ) :
    u ∈ (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker ↔ (u : R) - 1 ∈ I := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Ideal.Quotient.eq]
  simp

section Chars

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem congU_mono {I J : Ideal (RInt F E)} (h : I ≤ J) : congU F E I ≤ congU F E J := by
  apply Subgroup.map_mono
  intro u hu
  rw [mem_kerRed] at hu ⊢
  exact h hu

theorem congN_dvd {M N : ℕ} (h : M ∣ N) : congN F E N ≤ congN F E M := by
  apply congU_mono
  rw [Ideal.span_singleton_le_span_singleton]
  exact_mod_cast (Nat.cast_dvd_cast (α := RInt F E) h)

variable (L : Type) [Field L]

abbrev Chr : Type := (AfE F E)ˣ →* Lˣ

def openChr : Subgroup (Chr F E L) where
  carrier := {ξ | ∃ N : ℕ, 0 < N ∧ congN F E N ≤ ξ.ker}
  one_mem' := ⟨1, Nat.one_pos, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    exact ⟨M * N, Nat.mul_pos hM hN,
      (kills Lˣ (congN F E (M * N))).mul_mem ((congN_dvd F E (Dvd.intro _ rfl)).trans ha)
        ((congN_dvd F E (Dvd.intro_left _ rfl)).trans hb)⟩
  inv_mem' := by
    rintro a ⟨M, hM, ha⟩
    exact ⟨M, hM, (kills Lˣ (congN F E M)).inv_mem ha⟩

def finChar : Subgroup (Chr F E L) :=
  kills Lˣ (ratId F E).range ⊓ openChr F E L ⊓ CommGroup.torsion (Chr F E L)

def tupGrp (S : Set ℕ) : Subgroup (Chr F E L) :=
  finChar F E L ⊓ kills Lˣ (idF F E).range ⊓ (⨅ v : HeightOneSpectrum (𝓞 F), kills Lˣ (wildAt E v)) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : ¬ GoodPl E S v), kills Lˣ (inertAt E v)

def hostS (q d g₁ g₂ : ℕ) (T : Set ℕ) : Set ℕ := {2, q, d, g₁, g₂} ∪ T

abbrev Tup (S : Set ℕ) : Type := ↥(tupGrp F E L S)

def mu0 (S : Set ℕ) : Tup F E L S := 1

end Chars

section Ram

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

def Qprime (ξ : Chr F E L) : Set (HeightOneSpectrum (𝓞 F)) := {v | ¬ inertAt E v ≤ ξ.ker}

def QprimeN (ξ : Chr F E L) : Set ℕ := plc '' Qprime ξ

def InertOrd (ξ : Chr F E L) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Prop :=
  ∀ m : ℕ, (∀ x ∈ inertAt E v, ξ x ^ m = 1) ↔ n ∣ m

def TrivAt (ξ : Chr F E L) (v : HeightOneSpectrum (𝓞 F)) : Prop := suppAt E v ≤ ξ.ker

def IsBaseChar (p : ℕ) (δ : Chr F E L) : Prop :=
  p.Prime ∧ ∀ v : HeightOneSpectrum (𝓞 F), (plc v = p → InertOrd δ v 15) ∧ (plc v ≠ p → v ∉ Qprime δ)


variable (F E) in
def toRInt : 𝓞 E →+* RInt F E :=
  ((inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap (𝓞 E) E)).codRestrict (RInt F E)
    fun b => Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E b, b, rfl⟩, rfl⟩)

def IsResChar (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal →
  ∀ (u : (RInt F E)ˣ) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a →
    Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
    (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) →
    (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)) →
    ξ (Units.map (RInt F E).subtype.toMonoidHom u) = χ a


open scoped Classical in
open Classical in
def resChar (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ :=
  if h : ∃ χ, IsResChar ξ P χ then h.choose else 1

end Ram

section Tilde

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

def conjId (σ : E →ₐ[F] E) : (AfE F E)ˣ →* (AfE F E)ˣ :=
  Units.map (sigR σ (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

def h90 (σ : E →ₐ[F] E) : (AfE F E)ˣ →* (AfE F E)ˣ := MonoidHom.id _ / conjId σ

def U1 (σ : E →ₐ[F] E) : Subgroup (AfE F E)ˣ := (MonoidHom.id _ * conjId σ).ker


open scoped Classical in
open Classical in
def tilde (σ : E →ₐ[F] E) (ξ : Chr F E L) : (h90 σ).range →* Lˣ :=
  if h : (h90 σ).ker ≤ ξ.ker then
    (h90 σ).rangeRestrict.liftOfSurjective (h90 σ).rangeRestrict_surjective
      ⟨ξ, by rw [MonoidHom.ker_rangeRestrict]; exact h⟩
  else 1


open scoped Classical in
open Classical in
def detTw (σ : E →ₐ[F] E) (ξ : Chr F E L) {n : ℕ} (g : GL (Fin n) (AfE F E)) : Lˣ :=
  if h : Matrix.GeneralLinearGroup.det g ∈ (h90 σ).range then tilde σ ξ ⟨_, h⟩ else 1

end Tilde

section Maps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : Set ℕ}

def deAt (p : ℕ) (δ0 δ0' : Tup F E K S) (w : HeightOneSpectrum (𝓞 K)) : Tup F E K S :=
  if plc w = p then δ0' else δ0

def muTw (p : ℕ) (δ0 δ0' : Tup F E K S) (ψ : HeightOneSpectrum (𝓞 K) → Tup F E K S)
    (w : HeightOneSpectrum (𝓞 K)) : Tup F E K S := deAt p δ0 δ0' w * ψ w

end Maps

section Ref

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

structure IsMu0 (σ : E →ₐ[F] E) (Ψ : Finset (E →+* L)) (e : (E →+* L) → ℤ) (G : Set ℕ) (μ : Chr F E L) : Prop where
  isOpen : μ ∈ openChr F E L
  rat : ∀ a : Eˣ, ((μ (ratId F E a) : Lˣ) : L) = ∏ τ ∈ Ψ, (τ (a : E) / τ (σ (a : E))) ^ e τ
  trivF : (idF F E).range ≤ μ.ker
  tame : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ μ.ker
  ram : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ Qprime μ ↔ plc v ∈ G

def chiOf (μ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ := (resChar μ P)⁻¹

end Ref

end Formalism.L2.DIV

end
end

