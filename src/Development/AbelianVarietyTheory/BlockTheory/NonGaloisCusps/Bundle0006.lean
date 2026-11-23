module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationOverSumChar
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RepresentationOverSumChar

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

section Generic

variable {O Γ : Type} [CommRing O] [Group Γ]

def blockSum {r : ℕ} (t : ℕ) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) :
    Γ →* Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O where
  toFun g := Matrix.fromBlocks ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) 0 0
    (Matrix.diagonal fun c : Fin t => ((χ ((c : ℕ) + 1) g : Oˣ) : O))
  map_one' := by simp
  map_mul' g h := by
    simp [Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal]

def repOver (K : Type) [CommRing K] [Algebra O K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Γ →* Matrix n n O) : Representation K Γ (n → K) where
  toFun g := Matrix.toLin' ((M g).map (algebraMap O K))
  map_one' := by
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem charpoly_blockSum {r : ℕ} (t : ℕ) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (g : Γ) :
    (blockSum t ρ χ g).charpoly =
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).charpoly *
        ∏ c ∈ Finset.Icc 1 t, (X - C ((χ c g : Oˣ) : O)) := by
  have h : (blockSum t ρ χ g).charpoly =
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).charpoly *
        (Matrix.diagonal fun c : Fin t => ((χ ((c : ℕ) + 1) g : Oˣ) : O)).charpoly :=
    Matrix.charpoly_fromBlocks_zero₂₁ _ _ _
  rw [h, Matrix.charpoly_diagonal, Fin.prod_univ_eq_prod_range (fun c => X - C ((χ (c + 1) g : Oˣ) : O)) t,
    Finset.range_eq_Ico, Finset.prod_Ico_add' (fun c => X - C ((χ c g : Oˣ) : O)) 0 t 1]
  rfl

end Generic

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def FrobeniusMatrixCompatible (i : N.Loc) (x : N.X i) {n : Type} [Fintype n] [DecidableEq n]
    (M : GE N →* Matrix n n (N.O i)) : Prop :=
  ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → (M σ).charpoly = heckePol N i x w

def IsRx (i : N.Loc) (x : N.X i) {n : Type} [Fintype n] [DecidableEq n]
    (M : GE N →* Matrix n n (N.O i)) : Prop :=
  Continuous (fun g => M g) ∧ (repOver (KK N i) M).IsSemisimpleRepresentation ∧ FrobeniusMatrixCompatible N i x M

def sumChi (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    GE N →* Matrix (Fin R.r ⊕ Fin R.t) (Fin R.r ⊕ Fin R.t) (N.O i) :=
  blockSum R.t ρ (N.chi i)

def IsContRep (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)))

def IsRhoAt (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  FrobeniusMatrixCompatible N i π (sumChi N i ρ)

def IsSSSum (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  (repOver (KK N i) (sumChi N i ρ)).IsSemisimpleRepresentation

def IsComplement (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  IsRhoAt N i π ρ ∧ IsSSSum N i ρ ∧ IsContRep N i ρ

def SplitsAs (i : N.Loc) (rπ : GE N →* GL (Fin R.nV) (N.O i)) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] (Fin R.r ⊕ Fin R.t → KK N i), ∀ g u,
    e (repOver (KK N i) ((Units.coeHom _).comp rπ) g u) = repOver (KK N i) (sumChi N i ρ) g (e u)

theorem isRhoAt_iff (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    IsRhoAt N i π ρ ↔ ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      ((ρ σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)) = heckePol N i π w := by
  simp only [IsRhoAt, FrobeniusMatrixCompatible, sumChi, charpoly_blockSum]

theorem isRhoAt_of_splitsAs (i : N.Loc) (π : N.X i) (rπ : GE N →* GL (Fin R.nV) (N.O i))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) (hr : FrobeniusMatrixCompatible N i π ((Units.coeHom _).comp rπ))
    (hs : SplitsAs N i rπ ρ) : IsRhoAt N i π ρ := by
  obtain ⟨e, he⟩ := hs
  intro w hw B σ hB hσ
  rw [← hr w hw B σ hB hσ]
  apply Polynomial.map_injective (algebraMap (N.O i) (KK N i)) (IsFractionRing.injective _ _)
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, ← Matrix.charpoly_toLin', ← Matrix.charpoly_toLin',
    ← LinearEquiv.charpoly_conj e]
  congr 1
  refine LinearMap.ext fun u => ?_
  have := he σ (e.symm u)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.IndefiniteRowSideFullHecke.RepresentationOverSumChar

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

section Conj

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {c : Ω ≃+* Ω}

theorem conj_conj (hc : IsCMConjOm E Ω c) (x : Ω) : c (c x) = x := by
  obtain ⟨⟨j, hj⟩, -⟩ := hc
  apply j.injective
  rw [hj, hj]
  simp

theorem conj_symm (hc : IsCMConjOm E Ω c) (x : Ω) : c.symm x = c x := by
  rw [RingEquiv.symm_apply_eq, conj_conj hc]

def conjElt (hc : IsCMConjOm E Ω c) (g : G E Ω) : G E Ω :=
  AlgEquiv.ofRingEquiv (f := (c.symm.trans g.toRingEquiv).trans c) (fun x => by
    obtain ⟨y, hy⟩ := hc.2 x
    change c (g (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
    rw [conj_symm hc, hy, AlgEquiv.commutes, ← hy, conj_conj hc])

theorem conjElt_apply (hc : IsCMConjOm E Ω c) (g : G E Ω) (x : Ω) :
    conjElt hc g x = c (g (c.symm x)) := rfl

def conjHom (hc : IsCMConjOm E Ω c) : G E Ω →* G E Ω where
  toFun := conjElt hc
  map_one' := by
    ext x
    simp [conjElt_apply]
  map_mul' g h := by
    ext x
    simp [conjElt_apply]

end Conj

section Rep

variable {Γ : Type} [Group Γ] {A : Type} [CommRing A] {n : ℕ}

def scalGL : Aˣ →* GL (Fin n) A :=
  Units.map (Matrix.scalar (Fin n) : A →+* Matrix (Fin n) (Fin n) A).toMonoidHom

theorem scalGL_comm (a : Aˣ) (M : GL (Fin n) A) : Commute (scalGL a) M := by
  apply Units.ext
  exact (Matrix.scalar_commute (a : A) (fun b => mul_comm _ b) (M : Matrix (Fin n) (Fin n) A)).eq

def twist (ρ : Γ →* GL (Fin n) A) (χ : Γ →* Aˣ) : Γ →* GL (Fin n) A where
  toFun g := scalGL (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (scalGL (χ h)),
      (scalGL_comm (χ h) (ρ g)).eq, mul_assoc]

def transGL (M : GL (Fin n) A) : GL (Fin n) A where
  val := (M : Matrix (Fin n) (Fin n) A).transpose
  inv := ((M⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

def dual (ρ : Γ →* GL (Fin n) A) : Γ →* GL (Fin n) A where
  toFun g := transGL (ρ g⁻¹)
  map_one' := by
    apply Units.ext
    simp [transGL]
  map_mul' g h := by
    apply Units.ext
    simp only [transGL, mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul]

def IsoLat (ρ ρ' : Γ →* GL (Fin n) A) : Prop :=
  ∃ P : GL (Fin n) A, ∀ g, P * ρ g = ρ' g * P

end Rep

variable (D : _root_.Formalism.BasicNotions.D7)

def cycField (l : ℕ) : IntermediateField D.host.E D.nd.Om :=
  IntermediateField.adjoin D.host.E {x : D.nd.Om | x ^ l = 1}

def UnramifiedIn (l : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ^ 2

def NC (l : ℕ) : Prop :=
  l = 2 ∨ UnramifiedIn D l ∨ D.R.t * D.R.r < Module.finrank D.host.E ↥(cycField D l)

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

end
end

