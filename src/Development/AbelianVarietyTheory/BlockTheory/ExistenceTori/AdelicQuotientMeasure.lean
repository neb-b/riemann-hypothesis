module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped TensorProduct Matrix ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicQuotientClasses

section General

variable {H : Type} [Group H] (Γ : Subgroup H)

variable [MeasurableSpace H]

end General

def unitaryOf {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) :
    Subgroup (GL (Fin n) R) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) R)ᵀ * J * (g : Matrix (Fin n) (Fin n) R).map s = J}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul] at ha hb ⊢
    calc _ = (b : Matrix (Fin n) (Fin n) R)ᵀ * ((a : Matrix (Fin n) (Fin n) R)ᵀ * J *
              (a : Matrix (Fin n) (Fin n) R).map s) * (b : Matrix (Fin n) (Fin n) R).map s := by
            simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * (a : Matrix (Fin n) (Fin n) R)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have h2 : (a : Matrix (Fin n) (Fin n) R).map s * ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map s
        = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv]; simp
    conv_lhs => rw [← ha]
    calc _ = (((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * (a : Matrix (Fin n) (Fin n) R)ᵀ) * J *
          ((a : Matrix (Fin n) (Fin n) R).map s *
            ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map s) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, h2]; simp

def unitaryMap {R R' : Type} [CommRing R] [CommRing R'] (s : R →+* R) (s' : R' →+* R') (φ : R →+* R')
    (hφ : ∀ x, φ (s x) = s' (φ x)) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) :
    unitaryOf s J →* unitaryOf s' (J.map φ) :=
  ((Matrix.GeneralLinearGroup.map φ).comp (unitaryOf s J).subtype).codRestrict _ fun g => by
    have h : ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ * J *
        ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map s = J := g.2
    have h' := congrArg (fun M : Matrix (Fin n) (Fin n) R => M.map φ) h
    simp only [Matrix.map_mul] at h'
    have e : (((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map s).map φ =
        (((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map φ).map s' := by
      ext a b; simp [hφ]
    rw [e, Matrix.transpose_map] at h'
    exact h'

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def AfE : Type := GlobalTheory.AdLat.RA (maximalRealSubfield E) E

abbrev AfF : Type := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)

instance : CommRing (AfE E) := inferInstanceAs (CommRing (AfF E ⊗[maximalRealSubfield E] E))
instance : Algebra (AfF E) (AfE E) := inferInstanceAs (Algebra (AfF E) (AfF E ⊗[maximalRealSubfield E] E))

instance : TopologicalSpace (AfE E) := moduleTopology (AfF E) (AfE E)

def toAf : E →+* AfE E :=
  (Algebra.TensorProduct.includeRight :
    E →ₐ[maximalRealSubfield E] AfF E ⊗[maximalRealSubfield E] E).toRingHom

def cj : E →+* E := (IsCMField.complexConj E : E →+* E)

def cjAf : AfE E →+* AfE E := (GlobalTheory.AdLat.sg (AfF E) (IsCMField.complexConj E)).toRingHom

theorem toAf_cj (x : E) : toAf E (cj E x) = cjAf E (toAf E x) := by
  change (1 : AfF E) ⊗ₜ[maximalRealSubfield E] (IsCMField.complexConj E x) =
    GlobalTheory.AdLat.sg (AfF E) (IsCMField.complexConj E) ((1 : AfF E) ⊗ₜ[maximalRealSubfield E] x)
  simp [GlobalTheory.AdLat.sg]

theorem emb_cj (τ : E →+* ℂ) (x : E) : τ (cj E x) = starRingEnd ℂ (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

variable {E} {n : ℕ}

def IsHermGram (G : Matrix (Fin n) (Fin n) E) : Prop := (∀ a b, G b a = cj E (G a b)) ∧ G.det ≠ 0

variable (G : Matrix (Fin n) (Fin n) E)

abbrev URat : Type := unitaryOf (cj E) G

abbrev UReal (w : InfinitePlace E) : Type := unitaryOf (starRingEnd ℂ) (G.map w.embedding)

abbrev UFin : Type := unitaryOf (cjAf E) (G.map (toAf E))

def UAd : Type := (∀ w : InfinitePlace E, UReal G w) × UFin G

instance : Group (UAd G) := inferInstanceAs (Group ((∀ w : InfinitePlace E, UReal G w) × UFin G))
instance : TopologicalSpace (UAd G) :=
  inferInstanceAs (TopologicalSpace ((∀ w : InfinitePlace E, UReal G w) × UFin G))
instance : MeasurableSpace (UAd G) := borel (UAd G)

def diag : URat G →* UAd G :=
  MonoidHom.prod
    (Pi.monoidHom fun w : InfinitePlace E =>
      unitaryMap (cj E) (starRingEnd ℂ) w.embedding (emb_cj E w.embedding) G)
    (unitaryMap (cj E) (cjAf E) (toAf E) (toAf_cj E) G)

def ratPts : Subgroup (UAd G) := (diag G).range

def sgnMat (n p : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if (i : ℕ) < p then 1 else -1

def lieCube (n p : ℕ) (r : ℝ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | Xᵀ * sgnMat n p + sgnMat n p * X.map (starRingEnd ℂ) = 0 ∧ (∀ i, |(X i i).im| ≤ r) ∧
    ∀ i j, i < j → |(X i j).re| ≤ r ∧ |(X i j).im| ≤ r}

def IsOrthoFrame (w : InfinitePlace E) (p : ℕ) (b : GL (Fin n) ℂ) : Prop :=
  p ≤ n ∧ (b : Matrix (Fin n) (Fin n) ℂ)ᵀ * G.map w.embedding *
    (b : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) = sgnMat n p

def cubeNhd (K : Subgroup (UFin G)) (p : InfinitePlace E → ℕ) (b : InfinitePlace E → GL (Fin n) ℂ) (r : ℝ) :
    Set (UAd G) :=
  {g | g.2 ∈ K ∧ ∀ w, ∃ X ∈ lieCube n (p w) r,
    (((b w)⁻¹ * (g.1 w : GL (Fin n) ℂ) * b w : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp X}

def IsNormalised (K : Subgroup (UFin G)) (μ : Measure (UAd G)) : Prop :=
  IsOpen (K : Set (UFin G)) ∧ IsCompact (K : Set (UFin G)) ∧ μ.IsHaarMeasure ∧
    ∃ (p : InfinitePlace E → ℕ) (b : InfinitePlace E → GL (Fin n) ℂ), (∀ w, IsOrthoFrame G w (p w) (b w)) ∧
      Tendsto (fun r : ℝ => μ (cubeNhd G K p b r) /
        ENNReal.ofReal ((2 * r) ^ (n ^ 2 * Fintype.card (InfinitePlace E)))) (𝓝[>] 0) (𝓝 1)

def IsVolDatum (K : Subgroup (UFin G)) (μ : Measure (UAd G)) (D : Set (UAd G)) : Prop :=
  IsNormalised G K μ ∧ IsFundamentalDomain (ratPts G) D μ

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicQuotientClasses
