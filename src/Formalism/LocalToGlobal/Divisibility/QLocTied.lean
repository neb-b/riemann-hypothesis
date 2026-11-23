module

public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0007
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.LocalRingCardinality.DataIdx
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0004

@[expose] public section

noncomputable section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host
open scoped ComplexConjugate

namespace Formalism.L2.DIV

namespace QLoc

section Local

variable {F : Type} [Field F]

def chi0 (δ : Fˣ →* ℂˣ) (x : F) : ℂ :=
  open Classical in if h : x = 0 then 0 else ((δ (Units.mk0 x h) : ℂˣ) : ℂ)

def bAA {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin r) (Fin r) F :=
  x.submatrix (Fin.castAdd d) (Fin.castAdd c)
def bAD {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin r) (Fin c) F :=
  x.submatrix (Fin.castAdd d) (Fin.natAdd r)
def bDA {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin d) (Fin r) F :=
  x.submatrix (Fin.natAdd r) (Fin.castAdd c)
def bDD {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Matrix (Fin d) (Fin c) F :=
  x.submatrix (Fin.natAdd r) (Fin.natAdd r)

variable (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ)

def parJ (r c : ℕ) : Set (GL (Fin (r + c)) F) :=
  {k | k ∈ GLint O (r + c) ∧ bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ IIset O ϖ}

def lamJ (δ : Fˣ →* ℂˣ) {r c : ℕ} (k : GL (Fin (r + c)) F) : ℂ :=
  chi0 δ (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det

def phiQ (δ : Fˣ →* ℂˣ) (r d c : ℕ) (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : ℂ :=
  open Classical in
  if bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c then
    (chi0 δ (bAA x).det)⁻¹ else 0

def IsSphFn {c : ℕ} (χ : Fin c → F → ℂ) (φ : GL (Fin c) F → ℂ) : Prop :=
  ∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ k ∈ GLint O c,
    φ (b * k) = ∏ i : Fin c, χ i ((b : Matrix (Fin c) (Fin c) F) i i) *
      ((nrm ((b : Matrix (Fin c) (Fin c) F) i i) ^ (((c : ℝ) - 1) / 2 - (i : ℕ)) : ℝ) : ℂ)

def satC (ν : ℕ → Fˣ →* ℂˣ) (t c : ℕ) (a : Fin c) (x : F) : ℂ :=
  chi0 (ν ((a : ℕ) / t + 1)) x * ((nrm x ^ ((((a : ℕ) % t : ℕ) : ℝ) - ((t : ℝ) - 1) / 2) : ℝ) : ℂ)

variable [TopologicalSpace F] [IsTopologicalRing F]

structure IsUnrM (r c : ℕ) (χ : Fin c → F → ℂ) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : GL (Fin r) F × GL (Fin c) F →* (V ≃ₗᵢ[ℂ] V)) : Prop where
  smooth : ∀ x : V, IsOpen {m | ρ m x = x}
  irred : ∀ W : Submodule ℂ V, (∀ m, ∀ x ∈ W, ρ m x ∈ W) → W = ⊥ ∨ W = ⊤
  sph : ∃ v₀ : V, ‖v₀‖ = 1 ∧ (∀ k₁ ∈ GLint O r, ∀ k₂ ∈ GLint O c, ρ (k₁, k₂) v₀ = v₀) ∧
    ∃ (φ : GL (Fin c) F → ℂ) (κ : Measure (GL (Fin c) F)), IsSphFn O nrm χ φ ∧ κ.IsMulLeftInvariant ∧
      κ (GLint O c : Set (GL (Fin c) F)) = 1 ∧
      ∀ g : GL (Fin c) F, inner ℂ v₀ (ρ (1, g) v₀) = ∫ k in (GLint O c : Set (GL (Fin c) F)), φ (k * g) ∂κ

def typeSp (δ : Fˣ →* ℂˣ) (r c : ℕ) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : GL (Fin r) F × GL (Fin c) F →* (V ≃ₗᵢ[ℂ] V)) : Submodule ℂ (GL (Fin (r + c)) F → V) where
  carrier := {f | (∀ (p : GL (Fin (r + c)) F) (m₁ : GL (Fin r) F) (m₂ : GL (Fin c) F),
      bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 →
      bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = (m₁ : Matrix (Fin r) (Fin r) F) →
      bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = (m₂ : Matrix (Fin c) (Fin c) F) → ∀ g,
      f (p * g) = (((nrm (m₁ : Matrix (Fin r) (Fin r) F).det ^ ((c : ℝ) / 2) *
          nrm (m₂ : Matrix (Fin c) (Fin c) F).det ^ (-(r : ℝ) / 2) : ℝ) : ℂ) *
        ((δ (Matrix.GeneralLinearGroup.det m₂) : ℂˣ) : ℂ)) • ρ (m₁, m₂) (f g)) ∧
    ∀ k ∈ parJ O ϖ r c, ∀ g, f (g * k) = lamJ δ k • f g}
  zero_mem' := ⟨fun _ _ _ _ _ _ _ => by simp, fun _ _ _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨fun p m₁ m₂ a b c g => ?_, fun k hk g => ?_⟩
    · simp only [Pi.add_apply, h1 p m₁ m₂ a b c g, h3 p m₁ m₂ a b c g, map_add (f := _), smul_add]
    · simp only [Pi.add_apply, h2 k hk g, h4 k hk g, smul_add]
  smul_mem' := by
    rintro z f ⟨h1, h2⟩
    refine ⟨fun p m₁ m₂ a b c g => ?_, fun k hk g => ?_⟩
    · simp only [Pi.smul_apply, h1 p m₁ m₂ a b c g, map_smul]
      exact smul_comm _ _ _
    · simp only [Pi.smul_apply, h2 k hk g]
      exact smul_comm _ _ _

def mcoef {n : ℕ} (μ : Measure (GL (Fin n) F)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (f : GL (Fin n) F → V) (g : GL (Fin n) F) : ℂ :=
  ∫ k in (GLint O n : Set (GL (Fin n) F)), inner ℂ (f k) (f (k * g)) ∂μ

def IsTypeDim (δ : Fˣ →* ℂˣ) (ν : ℕ → Fˣ →* ℂˣ) (r t j n : ℕ) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
    (ρ : GL (Fin r) F × GL (Fin (j * t)) F →* (V ≃ₗᵢ[ℂ] V)),
    IsUnrM O nrm r (j * t) (satC nrm ν t (j * t)) ρ ∧ n = Module.finrank ℂ (typeSp O ϖ nrm δ r (j * t) ρ)

def IsStep [MeasurableSpace F] (δ : Fˣ →* ℂˣ) (ν : ℕ → Fˣ →* ℂˣ) (r t j : ℕ) (z : ℂ) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
    (ρ : GL (Fin r) F × GL (Fin (j * t)) F →* (V ≃ₗᵢ[ℂ] V)),
    IsUnrM O nrm r (j * t) (satC nrm ν t (j * t)) ρ ∧ ∃ f ∈ typeSp O ϖ nrm δ r (j * t) ρ,
    ∃ (μ : Measure (GL (Fin (r + j * t)) F)) (dx : Measure (Matrix (Fin (r + (j + 1) * t)) (Fin (r + j * t)) F)),
      μ.IsMulLeftInvariant ∧ μ (parJ O ϖ r (j * t)) = 1 ∧ mcoef O μ f 1 = 1 ∧
      dx.IsAddLeftInvariant ∧ dx (intMat O (r + (j + 1) * t) (r + j * t)) = 1 ∧
      z = localZ μ dx (ν (j + 1) * δ) nrm (phiQ O ϖ δ r ((j + 1) * t) (j * t)) (phiQ O ϖ δ r ((j + 1) * t) (j * t))
        (mcoef O μ f)

end Local

def zVal (q : ℝ) (r t j : ℕ) (x : ℕ → ℂ) : ℂ :=
  ((q ^ (-((j * t * r : ℕ) : ℤ)) * MainNotions.ZetaProductPairs.qE q 1 r * MainNotions.ZetaProductPairs.qE q (t + 1) (j * t) : ℝ) : ℂ) *
    ∏ i ∈ Finset.Ico 1 j, MainNotions.ZetaProductPairs.Lpair q t (x i / x j)

def zVal1 (q : ℝ) (r t : ℕ) : ℝ := MainNotions.ZetaProductPairs.qE q 1 r * q ^ (-((t * r : ℕ) : ℤ))

theorem zVal_one (q : ℝ) (r t : ℕ) (x : ℕ → ℂ) : zVal q r t 1 x = (zVal1 q r t : ℂ) := by
  have he : MainNotions.ZetaProductPairs.qE q (t + 1) (1 * t) = 1 := by
    unfold MainNotions.ZetaProductPairs.qE
    rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty]
  unfold zVal zVal1
  rw [Finset.Ico_self, Finset.prod_empty, mul_one, he, mul_one, Nat.one_mul]
  congr 1
  ring

section AtP

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

def OP : Subring (P.adicCompletion L) := (P.adicCompletionIntegers L).toSubring

def piP : (P.adicCompletion L)ˣ := atFin P (unif P)

def qP : ℕ := Ideal.absNorm P.asIdeal

def Deg1 : Prop := (qP P).Prime ∧ Valued.v ((qP P : ℕ) : P.adicCompletion L) = WithZero.exp (-1 : ℤ)

def IsNrm (nrm : AbsoluteValue (P.adicCompletion L) ℝ) : Prop :=
  ∀ x : (P.adicCompletion L)ˣ, (IsUnitAt P x → nrm x = 1) ∧ (IsUnifAt P x → nrm x = (qP P : ℝ)⁻¹)

def TypeDimAt (δ : (P.adicCompletion L)ˣ →* ℂˣ) (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ) (r t j n : ℕ) : Prop :=
  ∃ nrm, IsNrm P nrm ∧ IsTypeDim (OP P) (piP P : P.adicCompletion L) nrm δ ν r t j n

def StepAt (δ : (P.adicCompletion L)ˣ →* ℂˣ) (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ) (r t j : ℕ) (z : ℂ) : Prop :=
  ∃ nrm, IsNrm P nrm ∧
    letI : MeasurableSpace (P.adicCompletion L) := borel _
    IsStep (OP P) (piP P : P.adicCompletion L) nrm δ ν r t j z

structure IsDel (δ : (P.adicCompletion L)ˣ →* ℂˣ) : Prop where
  unitary : ∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1
  tame : ∀ x, IsUnitAt P x → Valued.v ((x : P.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) → δ x = 1
  ram : ¬ ∀ x, IsUnitAt P x → δ x = 1

structure IsNu (ν : (P.adicCompletion L)ˣ →* ℂˣ) : Prop where
  unitary : ∀ x, ‖((ν x : ℂˣ) : ℂ)‖ = 1
  unr : ∀ x, IsUnitAt P x → ν x = 1

end AtP

end QLoc

open QLoc

def ThmQ : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P →
    ∀ (δ : (P.adicCompletion L)ˣ →* ℂˣ) (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → (∀ i, IsNu P (ν i)) →
    ∀ r t j : ℕ, 1 ≤ t →
      (∀ n, TypeDimAt P δ ν r t j n → n = 1) ∧
      ∀ z, StepAt P δ ν r t j z → z = zVal (qP P) r t (j + 1) (fun i => ((ν i (piP P) : ℂˣ) : ℂ))

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

def delQ (Tp : TupTied D C nch) (μ : D.what₂.Tup) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    (P.adicCompletion D.host.E)ˣ →* ℂˣ := ((Tp.xi μ)⁻¹).loc P

def nuP (C : CharFrame D) (P : HeightOneSpectrum (𝓞 D.host.E)) (i : ℕ) : (P.adicCompletion D.host.E)ˣ →* ℂˣ :=
  if h : 1 ≤ i ∧ i ≤ D.R.m then ((C.mu0 ⟨i - 1, by omega⟩)⁻¹).loc P else 1

theorem nuP_succ (C : CharFrame D) (P : HeightOneSpectrum (𝓞 D.host.E)) (j : Fin D.R.m) :
    nuP C P (j.1 + 1) = ((C.mu0 j)⁻¹).loc P := by
  have hj := j.2
  unfold nuP
  rw [dite_eq_left ⟨by omega, by omega⟩]
  first
    | rfl
    | (congr 3; ext; simp)
    | (congr 2; ext; simp)

structure QLocTied (Tp : TupTied D C nch) (Z : DivX D)
    (PQ : ∀ μ, Z.QPl μ → HeightOneSpectrum (𝓞 D.host.E)) : Prop where

  qv_eq : ∀ μ v, Z.qv μ v = qP (PQ μ v)

  deg1 : ∀ μ v, Deg1 (PQ μ v)

  ram : ∀ μ v, ¬ (Tp.xi μ).UnrAt (PQ μ v)

  off_g : ∀ μ v k, ¬ OverP D.host (D.host.g k) (PQ μ v)

  nu_eq : ∀ μ v (i : Fin D.R.m), Z.nu μ v (i.1 + 1) = ((((C.mu0 i).val (PQ μ v))⁻¹ : ℂˣ) : ℂ)

  typeDim_eq : ∀ μ v j, j ≤ D.R.m →
    TypeDimAt (PQ μ v) (delQ Tp μ (PQ μ v)) (nuP C (PQ μ v)) D.R.r D.R.t j (Z.typeDim μ v j)

  ZQ_eq : ∀ μ v j, j < D.R.m →
    StepAt (PQ μ v) (delQ Tp μ (PQ μ v)) (nuP C (PQ μ v)) D.R.r D.R.t j (Z.ZQ μ v (j + 1))

  quotientLocalValueFirst_eq : ∀ μ v j, 1 ≤ j → j ≤ D.R.m →
    StepAt (PQ μ v) (delQ Tp μ (PQ μ v)) (fun _ => nuP C (PQ μ v) j) D.R.r D.R.t 0 (Z.quotientLocalValueFirst μ v)

def QLocTiedC {Tp : TupTied D C nch} {Z : DivX D} (T : DivisorCharacterCompatibility D C nch Tp Z)
    (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  (∀ μ v, Pv (T.eQPl μ v).1 ∈ aboveF (L := D.host.E) D.host.F (T.eQPl μ v).1) ∧
    QLocTied Tp Z fun μ v => Pv (T.eQPl μ v).1

structure QLocVal (Z : DivX D) : Prop where
  typeDim : ∀ μ v j, j ≤ D.R.m → Z.typeDim μ v j = 1
  ZQ : ∀ μ v j, 1 ≤ j → j ≤ D.R.m → Z.ZQ μ v j = zVal (Z.qv μ v) D.R.r D.R.t j (Z.nu μ v)
  quotientLocalValueFirst : ∀ μ v, Z.quotientLocalValueFirst μ v = (zVal1 (Z.qv μ v) D.R.r D.R.t : ℂ)

theorem isDel_delQ (Tp : TupTied D C nch) (μ : D.what₂.Tup) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (h : ¬ (Tp.xi μ).UnrAt P) : IsDel P (delQ Tp μ P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨n, hn, he⟩ := Tp.xi_fin μ
    have h1 : ((Tp.xi μ).loc P x) ^ n = 1 := by
      have : ((Tp.xi μ) ^ n).loc P x = 1 := by rw [show (Tp.xi μ) ^ n = 1 from he]; rfl
      rw [← this]
      simp [HChar.loc]
    have h2 : ‖(((Tp.xi μ).loc P x : ℂˣ) : ℂ)‖ ^ n = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1]; simp
    have h3 : ‖(((Tp.xi μ).loc P x : ℂˣ) : ℂ)‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h2
    change ‖((((Tp.xi μ).loc P x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, h3, inv_one]
  · intro x hx hx1
    change ((Tp.xi μ).loc P x)⁻¹ = 1
    exact inv_eq_one.mpr (Tp.xi_tame μ P x hx (by simpa using hx1))
  · intro h'
    exact h fun x hx => inv_eq_one.mp (h' x hx)

theorem isNu_nuP (C : CharFrame D) {P : HeightOneSpectrum (𝓞 D.host.E)} (h : ∀ k, ¬ OverP D.host (D.host.g k) P) (i : ℕ) :
    IsNu P (nuP C P i) := by
  unfold nuP
  split_ifs with hi
  · have hU := (C.isMu0 ⟨i - 1, by omega⟩).unitary.inv
    refine ⟨fun x => hU _, fun x hx => ?_⟩
    have h1 := (C.isMu0 ⟨i - 1, by omega⟩).unr P h x hx
    show ((C.mu0 ⟨i - 1, by omega⟩).loc P x)⁻¹ = 1
    rw [h1, inv_one]
  · exact ⟨fun x => by simp, fun x _ => rfl⟩

theorem QLocTied.nu_nuP {Tp : TupTied D C nch} {Z : DivX D} {PQ} (h : QLocTied Tp Z PQ) (μ : D.what₂.Tup) (v : Z.QPl μ)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) : Z.nu μ v i = ((nuP C (PQ μ v) i (piP (PQ μ v)) : ℂˣ) : ℂ) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j < D.R.m := by omega
  rw [h.nu_eq μ v ⟨j, hj⟩, nuP_succ C (PQ μ v) ⟨j, hj⟩]
  rfl

theorem QLocTied.val (hQ : ThmQ) {Tp : TupTied D C nch} {Z : DivX D} {PQ} (h : QLocTied Tp Z PQ) : QLocVal Z := by
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hm := D.R.two_le_m
  refine ⟨fun μ v j hj => ?_, fun μ v j h1 hj => ?_, fun μ v => ?_⟩
  · exact (hQ D.host.E (PQ μ v) (h.deg1 μ v) (delQ Tp μ (PQ μ v)) (nuP C (PQ μ v))
      (isDel_delQ Tp μ (h.ram μ v)) (fun i => isNu_nuP C (h.off_g μ v) i) D.R.r D.R.t j ht).1 _
      (h.typeDim_eq μ v j hj)
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hz := (hQ D.host.E (PQ μ v) (h.deg1 μ v) (delQ Tp μ (PQ μ v)) (nuP C (PQ μ v))
      (isDel_delQ Tp μ (h.ram μ v)) (fun i => isNu_nuP C (h.off_g μ v) i) D.R.r D.R.t j' ht).2 _
      (h.ZQ_eq μ v j' (by omega))
    rw [hz, h.qv_eq μ v]
    unfold zVal
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [h.nu_nuP μ v i hi.1 (by omega), h.nu_nuP μ v (j' + 1) (by omega) hj]
  · have hz := (hQ D.host.E (PQ μ v) (h.deg1 μ v) (delQ Tp μ (PQ μ v)) (fun _ => nuP C (PQ μ v) 1)
      (isDel_delQ Tp μ (h.ram μ v)) (fun _ => isNu_nuP C (h.off_g μ v) 1) D.R.r D.R.t 0 ht).2 _
      (h.quotientLocalValueFirst_eq μ v 1 le_rfl (by omega))
    rw [hz, zero_add, zVal_one, h.qv_eq μ v]

end Formalism.L2.DIV
