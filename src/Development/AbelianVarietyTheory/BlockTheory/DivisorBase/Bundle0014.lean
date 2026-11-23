module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdaptedStandardBasis
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def IsThetaWt (la : Weight Dw) (n : ℕ) : Prop :=
  8 ∣ n ∧ (∀ τ, Antitone (la τ)) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) < Dw.p → ((n / 2 : ℕ) : ℤ) ≤ la τ i) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), Dw.p ≤ (i : ℕ) → la τ i ≤ -((n / 2 : ℕ) : ℤ)) ∧
    ∀ τ (i k : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (k : ℕ) = Dw.p → (n : ℤ) + 2 < la τ i - la τ k

end Weights

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

def polyNorm {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : ℝ :=
  Real.sqrt (∑ s : c.F →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2)



variable {Xo c} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

end Family

section Constants

variable (D : D7) (large₂ : SizeData₂ D)

end Constants

section Statement

variable (D : D7) (large₂ : SizeData₂ D)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def badPlaces (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Formalism.L2.DIV.primesOf (((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F))

def IsReadingPlaces (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∃ pb : Fin 2 → 𝓞 D.host.E, (∀ i, (pb i : D.host.E) ∈ D.host.K) ∧ IsTypePlaces (D := D) D.host.g pb Pg

def IsBelow {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (b : Pg ≃ LevelCuspCharacters.Sq D.host) : Prop :=
  ∀ PP : Pg, (b PP).2.1.asIdeal = PP.1.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))

def IsFrameAtG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ), IsBaseFrame V β Λ ((D.host.g 0 * D.host.g 1) ^ c)

def datR (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ)
    (fr : Lev.Frm) : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  datY V.rank D.R.r D.R.t 0 hr Pg ∅ P (fun _ _ => 1) (fun _ => 1) fr

def eLin (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (e : Formalism.L2.DIV.G0 L.Pg L.r →₀ ℂ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := eAct V β L e
  map_add' F G := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' a F := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

theorem rank_le_first_space_rank (D : D7) : D.R.r ≤ (D.sp.Y 0).rank := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Ranks.rankY]

section Parts

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}

def rowPart (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (β : GL (Fin (D.sp.Y 0).rank) (EAf D))
    (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ) (e : Formalism.L2.DIV.G0 Pg D.R.r →₀ ℂ)
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  EEpart θ M (levG (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) : Set (GA D (D.sp.Y 0)))
    (levChi (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B))
    (eLin (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) e) (badPlaces D) c

end Parts

def gramIn (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) β.val *
    V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * β.val

def Matched (V V' : HSp D) (h : V'.rank = V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) : Prop :=
  ∃ y : GL (Fin V'.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
    (∀ PP ∈ Pg, Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) y = 1) ∧
    gramIn V' (β' * Formalism.L2.DIV.intGL D.host.F D.host.E V'.rank y) = (gramIn V β).submatrix (Fin.cast h) (Fin.cast h)

end GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt
open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def IsComplexData : Prop :=
  l.A = 1 ∧ ∀ σ, GoodEmb c σ → IsUnf (U σ) ∧
    (∃ Kf th hr, IsLevelK (V σ) l.M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictIsUnif (V σ) (dict σ) Kf th hr) ∧
    FinVol (V σ) ∧ ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D

def partLat (Z : Comp Xo c) (G : WTZ D.host.E) : Submodule (𝓞 c.F) (cuspW Xo c U G) :=
  (latOn U Z G).map ((Submodule.inclusion (cuspOn_le U Z G)).restrictScalars (𝓞 c.F))

def normRes (Z : Comp Xo c) (G : WTZ D.host.E) (σ : c.F →+* ℂ) (f : cuspOn U Z G) : ℝ :=
  petW U (xiR D) V dict G σ f

attribute [local instance high] Submodule.module

def degRes (Z : Comp Xo c) (G : WTZ D.host.E) : ℝ :=
  GlobalTheory.AllWt.deg (normRes U V dict Z G) (latOn U Z G)

def mass (Z : Comp Xo c) (σ : c.F →+* ℂ) : ℝ :=
  (muQ1 (V (goodOf c σ))
    (classesOver (V (goodOf c σ)) (dict (goodOf c σ)) (framesOn (U (goodOf c σ)) Z))).toReal

def Splits (G : WTZ D.host.E) : Prop :=
  (∀ F : cuspW Xo c U G, (F : Rul Xo c) = ∑ᶠ Z : Comp Xo c, FlatLine.idem Z * (F : Rul Xo c) ∧
    ∃ h : ∀ Z : Comp Xo c, FlatLine.idem Z * (F : Rul Xo c) ∈ cuspOn U Z G,
      (F ∈ latW U G ↔ ∀ Z, (⟨_, h Z⟩ : cuspOn U Z G) ∈ latOn U Z G)) ∧
  (iSupIndep (fun Z : Comp Xo c => cuspOn U Z G) ∧ ⨆ Z : Comp Xo c, cuspOn U Z G = cuspW Xo c U G) ∧
  iSupIndep (fun Z : Comp Xo c => partLat U Z G) ∧ ⨆ Z : Comp Xo c, partLat U Z G = latW U G

def Orthogonal (G : WTZ D.host.E) : Prop :=
  ∀ σ : c.F →+* ℂ,
    (∀ f : ∀ Z : Comp Xo c, cuspOn U Z G,
      petW U (xiR D) V dict G σ (∑ᶠ Z, (f Z : Rul Xo c)) ^ 2 = ∑ᶠ Z, normRes U V dict Z G σ (f Z) ^ 2) ∧
    ∀ (Z : Comp Xo c) (f : cuspOn U Z G),
      normRes U V dict Z G σ f ^ 2 = mass U V dict Z σ * normOn U (xiR D) V dict Z G σ f ^ 2

def Adds (G : WTZ D.host.E) : Prop :=
  (GoodW U (xiR D) V dict G ↔ ∀ Z, GoodOn U (xiR D) V dict Z G) ∧
  (GoodW U (xiR D) V dict G →
    (∀ Z, HasGram (normRes U V dict Z G)) ∧
    rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧
    degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, degRes U V dict Z G ∧
    (∀ Z, rankOn U Z G ≠ 0 → ∀ σ, 0 < mass U V dict Z σ) ∧
    degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, (degOn U (xiR D) V dict Z G -
      (rankOn U Z G : ℝ) / 2 * ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (finrank ℚ c.F : ℝ))))

theorem finite_comp : Finite (Comp Xo c) := CompFin.finite_comp Xo c

theorem partLat_le (Z : Comp Xo c) (G : WTZ D.host.E) : partLat U Z G ≤ latW U G := by
  rintro _ ⟨f, hf, rfl⟩
  exact (mem_latOn U).1 hf

end GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftedCharacterResidue
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def stabLat (V : HSp D) : Subgroup (GA D V) where
  carrier := {k | k ∈ GfC V ∧ ∀ z, (finHom V k).1.mulVec z ∈ latHat V ↔ z ∈ latHat V}
  one_mem' := ⟨(GfC V).one_mem, fun z => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(GfC V).mul_mem ha hb, fun z => ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ha', hb']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(GfC V).inv_mem ha, fun z => ?_⟩
    rw [← ha' ((finHom V a⁻¹).1.mulVec z), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.one_mulVec]

def prinLev (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ stabLat V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

variable (T : CoreJ D)

variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]

end GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LinearCoefficientData
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.L2.DIV
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsRecPlaces (D : D7) (Pg : Finset (Pl D.host.E)) : Prop :=
  ∀ PP, PP ∈ Pg ↔ ∃ kv : (Σ k : Fin 2, D.nd.PlG k), D.naut.plGw kv.1 kv.2 = PP

def resMap {E : Type} [Field E] [NumberField E] (p : ℕ) (PP : Pl E) (h : (p : 𝓞 E) ∈ PP.asIdeal) :
    ZMod p →+* kP PP :=
  ZMod.castHom (m := ringChar (kP PP))
    ((ringChar.spec (kP PP) p).1 (by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h)) (kP PP)

def idx {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) : (Σ k : Fin 2, D.nd.PlG k) :=
  ((h PP.1).1 PP.2).choose

theorem idx_spec {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) :
    D.naut.plGw (idx h PP).1 (idx h PP).2 = PP.1 :=
  ((h PP.1).1 PP.2).choose_spec

theorem idx_mem {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) :
    ((D.host.g (idx h PP).1 : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
  have h1 := D.naut.plGw_over (idx h PP).1 (idx h PP).2
  rw [idx_spec h PP] at h1
  exact h1

def toG0 {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (γ : G0g D.nd) : G0 Pg D.R.r := fun PP =>
  Matrix.GeneralLinearGroup.map (resMap (D.host.g (idx h PP).1) PP.1 (idx_mem h PP)) (γ (idx h PP))

def eCoef {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) : G0 Pg D.R.r →₀ ℂ :=
  Finsupp.mapDomain (toG0 h) D.ntypes.e0.coeff

def datR (V : HSp D) (hr : V.rank = D.R.r) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) (fr : Lev.Frm) :
    LevDat D.host.E ℂ V.rank :=
  Lev.datY V.rank D.R.r D.R.t 0 hr.ge Pg ∅ P (fun _ _ => 1) (fun _ => 1) fr

def eLin (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (e : G0 L.Pg L.r →₀ ℂ) :
    (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := Lev.eAct V β L e F
  map_add' F G := by
    funext x
    simp only [Lev.eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold Lev.actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' c F := by
    funext x
    simp only [Lev.eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold Lev.actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

theorem rank_zeroth_component_eq (D : D7) : (D.sp.Y 0).rank = D.R.r := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]; simp [Ranks.rankY]

abbrev InfFam (D : D7) : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

abbrev Eig (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

abbrev datE (D : D7) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) : LevDat D.host.E ℂ (D.sp.Y 0).rank :=
  datR (D.sp.Y 0) (rank_zeroth_component_eq D) Pg P Lev.Frm.B

abbrev datWj (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) :
    LevDat D.host.E ℂ (D.sp.W j).rank :=
  datR (D.sp.W j) (D.sp.W_rank j h1 h2) Pg P Lev.Frm.A

def EEc (θ : InfFam D) (M : Mult.DSModel (D.sp.Y 0) (Mult.parB (Mult.tparRec D) 0)) {Pg : Finset (Pl D.host.E)}
    (h : IsRecPlaces D Pg) (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (P : LevelP Pg D.R.r ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Eig D) : Submodule ℂ (Mult.MMap M) :=
  Mult.EEpart θ M (Lev.levG (D.sp.Y 0) β (datE D Pg P)) (Lev.levChi (D.sp.Y 0) β (datE D Pg P))
    (eLin (D.sp.Y 0) β (datE D Pg P) (eCoef h)) S c

def Wc (θ : InfFam D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M : Mult.DSModel (D.sp.W j) (Mult.parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) {Pg : Finset (Pl D.host.E)}
    (h : IsRecPlaces D Pg) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)) (P : LevelP Pg D.R.r ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Eig D) : Submodule ℂ (Mult.MMap M) :=
  Mult.Wpart θ j M (Lev.levG (D.sp.W j) β (datWj D j h1 h2 Pg P)) (Lev.levChi (D.sp.W j) β (datWj D j h1 h2 Pg P))
    (eLin (D.sp.W j) β (datWj D j h1 h2 Pg P) (eCoef h)) S c

end GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameInvariantLevelAction
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev OAf (D : D7) : Subring (EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def finR (V : HSp D) {r : ℕ} (hr : V.rank = r) : GA D V →* GL (Fin r) (EAf D) :=
  (Units.map (Matrix.reindexRingEquiv (EAf D) (finCongr hr)).toRingHom.toMonoidHom).comp (finE V)

def IsLatBasis (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) : Prop :=
  ∀ z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E, z ∈ latHat V ↔
    ∀ i, (Units.val (β⁻¹ : GL (Fin r) (EAf D))).mulVec
      (fun a => swapAE D (z (Fin.cast hr.symm a))) i ∈ OAf D

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Side (D : D7) (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ x : D.host.K, σ (D.embE (algebraMap D.host.K D.host.E x)) =
    D.what₂.embLL (D.embE (algebraMap D.host.K D.host.E x))

def SitsAt (D : D7) (σ : D.what₂.LL →+* ℂ) (τ τ' : D.what₂.Tau) : Prop :=
  ∃ t : D.host.E →+* D.what₂.LL, D.what₂.embLL.comp t = tauE D τ ∧ σ.comp t = tauE D τ'

def IsConjPar (D : D7) (j : ℕ) (σ : D.what₂.LL →+* ℂ) (S : D.what₂.Tau → SPar) : Prop :=
  ∀ τ', ∃ τ, SitsAt D σ τ τ' ∧ S τ' = parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)) τ

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def IsCover (V : HSp D) {G0 : Type} [Group G0] (Lift : G0 → GA D V → Prop) : Prop :=
  (∀ κ, κ ∈ levSet V 1 ↔ ∃ g, Lift g κ) ∧ (∀ g, ∃ κ, Lift g κ) ∧
    (∀ g g' κ, Lift g κ → Lift g' κ → g = g') ∧
    (∀ g g' κ κ', Lift g κ → Lift g' κ' → Lift (g * g') (κ * κ')) ∧
    ∀ κ, Lift 1 κ ↔ κ ∈ levSet V (D.host.g 0 * D.host.g 1)

variable (T : CoreJ D) (j : ℕ)

def rdK (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) (c : (T.U j s).Comp → ℂ) : T.R j →ₛₗ[s] (GA D (T.V j s) → ℂ) :=
  ((lieFac (T.Q.Dw j) (xiR D) (wtA w) : ℂ) •
    adel (T.V j s) (T.dict j s) (muPin (T.V j s) (T.dict j s) (T.mu j s) c)).comp (rdU (T.U j s))

variable [Algebra T.Q.c.F D.what₂.LL]

end GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets
end
end

