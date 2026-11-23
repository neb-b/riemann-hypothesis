module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LevelIndexFourierCharacter

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockPolyLevelMove
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial

section Lattice

variable {E : Type} [Field E] [NumberField E]

def unitLat (E : Type) [Field E] [NumberField E] (n : ℕ) : GenLat E n := ⟨stdLat E n⟩

def blockLat {n₁ n₂ : ℕ} (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) : GenLat E (n₁ + n₂) :=
  ⟨Λ₁.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
    Λ₂.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))⟩

end Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def LatAdm (l : Level H) (bad : ℕ) {n : ℕ} (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt l.M

def letL (Dw : Datum H) (n₁ n₂ : ℕ) (ℓ : LtN Dw n₁) : LtN Dw (n₁ + n₂) := ⟨ℓ.1, ℓ.2.1, Fin.castAdd n₂ ℓ.2.2⟩

def letR (Dw : Datum H) (n₁ n₂ : ℕ) (ℓ : LtN Dw n₂) : LtN Dw (n₁ + n₂) := ⟨ℓ.1, ℓ.2.1, Fin.natAdd n₁ ℓ.2.2⟩

def blockPoly {K : Type} [Field K] {n₁ n₂ : ℕ} (P₁ : MvPolynomial (LtN Dw n₁) K)
    (P₂ : MvPolynomial (LtN Dw n₂) K) : MvPolynomial (LtN Dw (n₁ + n₂)) K :=
  rename (letL Dw n₁ n₂) P₁ * rename (letR Dw n₁ n₂) P₂

def blockDat {K : Type} [Field K] {n₁ n₂ : ℕ} (w₁ : (Fin n₁ → LevQ Dw l) → K) (w₂ : (Fin n₂ → LevQ Dw l) → K) :
    (Fin (n₁ + n₂) → LevQ Dw l) → K :=
  fun q => w₁ (fun i => q (Fin.castAdd n₂ i)) * w₂ (fun j => q (Fin.natAdd n₁ j))

variable (Xo : Moduli Dw l) (c : Coeff l)

def IsBeta (Dw : Datum H) {l : Level H} (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β

def FreeOfLevel (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n), LatAdm l bad Λ →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), β ≠ 0 →
    ∀ (N N' : ℕ), Λ.LevOK N l.M → Λ.LevOK N' l.M →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v' : S),
      ShortValAt Xo c nab w Λ β N P y v → (ShortValAt Xo c nab w Λ β N' P y v' ↔ v' = v)

def BlockProduct (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₁ → LatAdm l bad Λ₂ →
    ∀ N : ℕ, Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    (LatAdm l bad (blockLat Λ₁ Λ₂) ∧ (blockLat Λ₁ Λ₂).LevOK N l.M) ∧
    ∀ (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ) (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F),
      P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
      blockPoly P₁ P₂ ∈ harmL c (blockLat Λ₁ Λ₂) (a₁ + a₂) ∧
      ∀ (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F)
        (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v₁ v₂ v : S),
        ShortValAt Xo c nab w₁ Λ₁ 1 N P₁ y v₁ → ShortValAt Xo c nab w₂ Λ₂ 1 N P₂ y v₂ →
        (ShortValAt Xo c nab (blockDat w₁ w₂) (blockLat Λ₁ Λ₂) 1 N (blockPoly P₁ P₂) y v ↔ v = v₁ * v₂)

def BlockBeta (Dw : Datum H) {l : Level H} (c : Coeff l) (bad : ℕ) : Prop :=
  (∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₁ → LatAdm l bad Λ₂ →
    ∀ β₁ β₂ β : c.F, IsBeta Dw c Λ₁ β₁ → IsBeta Dw c Λ₂ β₂ →
      (IsBeta Dw c (blockLat Λ₁ Λ₂) β ↔ ∃ ζ : c.F, IsOfFinOrder ζ ∧ β = ζ * (β₁ * β₂))) ∧
  ∀ (n₁ n₂ : ℕ) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₂ →
    IsBeta Dw c (unitLat E n₁) 1 ∧
      ∀ β : c.F, IsBeta Dw c (blockLat (unitLat E n₁) Λ₂) β ↔ IsBeta Dw c Λ₂ β

end GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockProductLattices
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices

open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Lat

variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}

def blockLat (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) : GenLat E (n₁ + n₂) where
  La := Λ₁.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
    Λ₂.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))

theorem mem_blockLat (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (v : Fin (n₁ + n₂) → E) :
    v ∈ (blockLat Λ₁ Λ₂).La ↔
      (fun j => v (Fin.castAdd n₂ j)) ∈ Λ₁.La ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ Λ₂.La := Iff.rfl

end Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def LatOK {n : ℕ} (bad M : ℕ) (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt M

end GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ConjugateFieldNorm
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped TensorProduct

section Adelic

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]

def cjF : E →ₐ[F] E :=
  { (IsCMField.complexConj E : E →+* E) with
    commutes' := fun x => by
      have h : algebraMap F E x ∈ maximalRealSubfield E := by
        rw [mem_maximalRealSubfield_iff]
        intro φ
        exact RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F E))) x
      exact (IsCMField.complexConj E).commutes ⟨_, h⟩ }

abbrev Af : Type := FiniteAdeleRing (𝓞 F) F

abbrev Ai : Type := InfiniteAdeleRing F

structure HSpace (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) where
  Gm : Matrix (Fin r) (Fin r) E
  Gm_herm : ∀ a b, cc (Gm a b) = Gm b a
  Gm_det : Gm.det ≠ 0
  L : Submodule (𝓞 E) (Fin r → E)
  L_fg : L.FG
  L_span : Submodule.span E (L : Set (Fin r → E)) = ⊤
  L_dual : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Gm x y)

def HSpace.std (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) : HSpace E r where
  Gm := 1
  Gm_herm a b := by by_cases h : a = b <;> simp [cc, Matrix.one_apply, h, eq_comm]
  Gm_det := by simp
  L := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)
  L_fg := Submodule.fg_pi fun _ => by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  L_span := by
    refine eq_top_iff.2 fun x _ => ?_
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (x i) : Fin r → E) = x i • (Pi.single i 1 : Fin r → E) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span fun k _ => ?_)
    by_cases h : k = i
    · subst h; simpa using Submodule.one_le.1 le_rfl
    · simp [h]
  L_dual x := by
    have hi : ∀ z : E, z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := fun z => by
      rw [Submodule.mem_one]
      exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
    have hh : ∀ y, herm (1 : Matrix (Fin r) (Fin r) E) x y = ∑ a, x a * cc (y a) := fun y => by
      simp [herm, Matrix.one_apply]
    constructor
    · intro hx y hy
      rw [hh]
      refine IsIntegral.sum _ fun a _ => ((hi _).1 (hx a trivial)).mul ?_
      exact ((hi _).1 (hy a trivial)).map (IsCMField.complexConj E : E →+* E).toIntAlgHom
    · intro h a _
      have := h (Pi.single a 1) fun k _ => by
        by_cases hk : k = a
        · subst hk; simpa using Submodule.one_le.1 le_rfl
        · simp [hk]
      rw [hh, Finset.sum_eq_single a (fun b _ hb => by simp [hb, cc]) (by simp)] at this
      exact (hi _).2 (by simpa [cc] using this)

variable {r : ℕ}

variable (A : Type) [CommRing A] [Algebra F A]

def incl : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom

def hermA (V : HSpace E r) (x y : Fin r → A ⊗[F] E) : A ⊗[F] E :=
  ∑ a, ∑ b, x a * incl F A (V.Gm a b) * Algebra.TensorProduct.map (AlgHom.id F A) (cjF F) (y b)

def UA (V : HSpace E r) : Subgroup (GL (Fin r) (A ⊗[F] E)) where
  carrier := {g | ∀ x y, hermA F A V (g.val.mulVec x) (g.val.mulVec y) = hermA F A V x y}
  one_mem' := fun x y => by simp
  mul_mem' := fun {g h} hg hh x y => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hh]
  inv_mem' := fun {g} hg x y => by
    rw [← hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.one_mulVec]

abbrev GA (V : HSpace E r) : Type := UA F (Ai F) V × UA F (Af F) V

def IsRat (V : HSpace E r) (γ : GL (Fin r) E) (g : GA F V) : Prop :=
  g.1.1.val = γ.val.map (incl F (Ai F)) ∧ g.2.1.val = γ.val.map (incl F (Af F))

def latHat (L : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → Af F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ ∃ x ∈ L, z = fun i => a ⊗ₜ[F] x i}

def levelK (V : HSpace E r) (N : ℕ) : Subgroup (GA F V) where
  carrier := {k | k.1 = 1 ∧ (∀ z, z ∈ latHat F V.L ↔ k.2.1.val.mulVec z ∈ latHat F V.L) ∧
    ∀ z ∈ latHat F V.L, ∃ w ∈ latHat F V.L, k.2.1.val.mulVec z - z = N • w}
  one_mem' := ⟨rfl, fun z => by simp, fun z _ => ⟨0, zero_mem _, by simp⟩⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    have e : ∀ z, (g * h).2.1.val.mulVec z = g.2.1.val.mulVec (h.2.1.val.mulVec z) := fun z => by
      rw [Matrix.mulVec_mulVec]; rfl
    refine ⟨by rw [Prod.fst_mul, g1, h1, mul_one], fun z => by rw [e, ← g2, ← h2], fun z hz => ?_⟩
    obtain ⟨w, hw, e1⟩ := h3 z hz
    obtain ⟨w', hw', e2⟩ := g3 _ ((h2 z).1 hz)
    exact ⟨w' + w, add_mem hw' hw, by rw [e, smul_add, ← e1, ← e2]; abel⟩
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    have e : ∀ z, g.2.1.val.mulVec ((g⁻¹).2.1.val.mulVec z) = z := fun z => by
      rw [Matrix.mulVec_mulVec]
      have : g.2.1.val * (g⁻¹).2.1.val = 1 := Units.mul_inv _
      rw [this, Matrix.one_mulVec]
    have s : ∀ z, z ∈ latHat F V.L ↔ (g⁻¹).2.1.val.mulVec z ∈ latHat F V.L := fun z => by
      rw [g2 ((g⁻¹).2.1.val.mulVec z), e]
    refine ⟨by rw [Prod.fst_inv, g1, inv_one], s, fun z hz => ?_⟩
    obtain ⟨w, hw, e1⟩ := g3 _ ((s z).1 hz)
    exact ⟨-w, neg_mem hw, by rw [smul_neg, ← e1, e]; abel⟩

def latAt (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (V : HSpace E r) (g : UA F (Af F) V) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ x : Fin r → E,
    (∃ z ∈ latHat F V.L, (fun i => incl F (Af F) (x i)) = g.1.val.mulVec z) ∧ v = a • x}

end Adelic

structure Nums (E : Type) [Field E] [NumberField E] where
  k : ℕ
  m : ℕ
  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  Nc : ℕ
  Nc_pos : 0 < Nc
  AA : FractionalIdeal (nonZeroDivisors (𝓞 E)) E
  Os : Subring ℂ

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Nums.r (R : Nums E) : ℕ := R.k + R.m - 1

abbrev Nums.J (R : Nums E) : Type := {j : ℕ // 1 ≤ j ∧ j ≤ R.m}

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F E]

structure CorePar (R : Nums E) : Type 1 where
  H : Host E
  l : Level H
  c : Coeff l
  Dw : R.J → Datum H
  Xo : ∀ j, Moduli (Dw j) l

  U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ R.r

  V : R.J → HSpace E R.r

  dict : ∀ j (σ : c.F →+* ℂ), GoodEmb c σ → GA F (V j) → Σ k, Frame ((U j σ).X k).Ψ R.r

  mu : ∀ j (σ : c.F →+* ℂ), GoodEmb c σ → GA F (V j) → ℂ

  Kf : ∀ j, Subgroup (GA F (V j))

  pi : Fin 2 → 𝓞 E

namespace CorePar

variable {F} {R : Nums E} (Q : CorePar F R)

end CorePar

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.NormFactorThetaValue
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation

attribute [local instance] Over.cartesianMonoidalCategory

section TwoLifts

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def IsTwoLifts (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T)) (x₁ x₂ : T ⟶ A)
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  Odd N ∧ x₁ ^ (N ^ 2) = 1 ∧ x₂ ^ (N ^ 2) = 1 ∧
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]))
    (s₁ s₂ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (U₁ U₂ : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
    α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧ α.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₁ U₁ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₁ s₁ s₂ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₂ U₂ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₂ s₂ F

end TwoLifts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def InKer {n : ℕ} (N : ℕ) (Lm : Submodule (𝓞 E) (Fin n → E))
    (hN : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Lm) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  (∀ j, a j ^ (N ^ 2) = 1) ∧
    ∀ (f : Lm →ₗ[𝓞 E] (Fin n → 𝓞 E)) (i : Fin n), ∏ j, a j ≫ Xo.univ.t.act.act (f ⟨_, hN j⟩ i) = 1

omit [NumberField E] [IsCMField E] in
theorem nsmul_single_mem_inter {n M N : ℕ} {Λ : Lat E n} (h : Λ.Admissible M N) (j : Fin n) :
    N • (Pi.single j 1 : Fin n → E) ∈ Λ.inter := by
  refine h.2.2 ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (single_mem_stdMod j)

omit [NumberField E] [IsCMField E] in
theorem nsmul_single_mem {n M N : ℕ} {Λ : Lat E n} (h : Λ.Admissible M N) (j : Fin n) :
    N • (Pi.single j 1 : Fin n → E) ∈ Λ.L := (nsmul_single_mem_inter h j).2

def InZ {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  InKer Xo N Λ.L (nsmul_single_mem h) a

def ptRes {S k : Type} [CommRing S] [CommRing k] (x0 : Sp S ⟶ Xo.X) (ψ : S →+* k) :
    ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl

def SplitsZ {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    {J : Type} (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  (∀ i, InZ Xo h (z i)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : S →+* k) (a : Fin n → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)),
      InZ Xo h a → ∃! i, ∀ j, a j = ptRes Xo x0 ψ ≫ z i j

def IsDivPt (N : ℕ) {T : Over Xo.X} (t t' : T ⟶ Xo.univ.t.G) : Prop :=
  t' ^ N = t ∧ KilledBy Xo (halfPart l N ^ 2) t'

def pairBox (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (k : ℤ)
    (P : MvPolynomial (LtN Dw n) c.F) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y k (F b) (colOf m b)

def normFactor {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (P : MvPolynomial (LtN Dw n) c.F) : c.F :=
  β⁻¹ * ((Λ.cardCenterZero (Dw.p + Dw.q) N : ℕ) : c.F)⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹

def SplitVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n N : ℕ} {Λ : Lat E n}
    (h : Λ.Admissible l.M N) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ∃ (r : ℕ) (z : Fin r → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (t' : (Fin n → NamedCl Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → NamedCl Dw l) → Fin r → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))),
    SplitsZ Xo h y.x z ∧
    (∀ t b, IsDivPt Xo N (levPtCl Xo y.x (t b)) (t' t b)) ∧
    (∀ t i b, IsTwoLifts Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (t' t b) (F t i b)) ∧
    v = algebraMap c.F S (normFactor c Λ N β P) *
      ∑ t ∈ levelIndex Dw l n, algebraMap c.F S (cf t) * ∑ i, pairBox Xo c nab y ((N : ℤ) ^ 2) P (F t i)

def LocVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n N : ℕ} {Λ : Lat E n}
    (h : Λ.Admissible l.M N) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S'),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ SplitVal Xo c nab y' h β cf P (φ v)

def InRange {n : ℕ} (Λ : Lat E n) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Λ.InGenus ∧ Λ.StdAt l.M ∧ β ≠ 0 ∧ P ∈ harmLat Dw c a Λ

def ThVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  InRange c Λ β a P ∧ ∃ h : Λ.Admissible l.M N, LocVal Xo c nab y h β cf P v

end GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ReflexNormIndexIdeal
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def indexIdeal (L' L : Submodule (𝓞 E) (Fin n → E)) : Ideal (𝓞 E) :=
  Ideal.span {a | ∃ g : (Fin n → E) →ₗ[E] (Fin n → E), (∀ x ∈ L', g x ∈ L) ∧ (a : E) = LinearMap.det g}

def latIdeal (Λ : Lat E n) : Ideal (𝓞 E) := indexIdeal Λ.L Λ.inter

omit [IsCMField E] in
theorem latIdeal_ne_bot (Λ : Lat E n) : latIdeal Λ ≠ ⊥ := by
  classical
  obtain ⟨S, hS⟩ := Λ.fg
  obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ (S ×ˢ (Finset.univ : Finset (Fin n)))
    (fun t => (t.1 t.2 : E))
  have hL : ∀ x ∈ Λ.L, (k : 𝓞 E) • x ∈ stdMod E n := by
    have : Λ.L ≤ (stdMod E n).comap (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) := by
      rw [← hS, Submodule.span_le]
      intro x hx
      refine mem_stdMod.2 fun j => ?_
      obtain ⟨a, ha⟩ := hk (x, j) (by simpa using hx)
      exact ⟨a, ha⟩
    exact fun x hx => this hx
  intro h
  have hm : (k : 𝓞 E) ^ n ∈ latIdeal Λ := by
    refine Ideal.subset_span ⟨((k : 𝓞 E) : E) • LinearMap.id, fun x hx => ⟨hL x hx, Λ.L.smul_mem _ hx⟩, ?_⟩
    rw [LinearMap.det_smul]
    simp
  rw [h, Ideal.mem_bot] at hm
  exact pow_ne_zero n (nonZeroDivisors.coe_ne_zero k) hm


variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

def reflexNorm (γ : E) : c.F := ∏ σ : E →+* ℂ, embF c σ γ ^ Dw.mult σ

def reflexIdeal (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 c.F) :=
  ∏ σ : E →+* ℂ, 𝔞.map (RingOfIntegers.mapRingHom (embF c σ)) ^ Dw.mult σ

def IsBe (𝔞 : Ideal (𝓞 E)) (β : c.F) : Prop :=
  (∃ b : 𝓞 c.F, (b : c.F) = β ∧ Ideal.span {b} = reflexIdeal Dw c 𝔞) ∧
    ∀ s : c.F →+* ℂ, ‖s β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ (Dw.p + Dw.q)

def IsBeLat (Λ : Lat E n) (β : c.F) : Prop := IsBe Dw c (latIdeal Λ) β

def ReflexLe : Prop := ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : c.F, IsBe Dw c 𝔞 β

theorem isBe_top : IsBe Dw c ⊤ 1 :=
  ⟨⟨1, rfl, by
    simp only [reflexIdeal, Ideal.map_top, Ideal.span_singleton_one]
    simp [← Ideal.one_eq_top]⟩, fun s => by simp⟩

variable {Dw c}


open scoped Classical in
def beIdeal (hK : ReflexLe Dw c) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : c.F :=
  if 𝔞 = ⊤ then 1 else (hK 𝔞 h𝔞).choose

def be (hK : ReflexLe Dw c) (Λ : Lat E n) : c.F := beIdeal hK (latIdeal Λ) (latIdeal_ne_bot Λ)

variable (Dw c)

end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
end
end

