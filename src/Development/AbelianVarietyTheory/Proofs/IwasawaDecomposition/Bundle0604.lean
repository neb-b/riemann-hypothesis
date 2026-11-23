module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieBasisExpCoordsDetBoundedAlongArc
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

theorem exists_chartLie_along : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U), ∃ v' : Fin M.n → (epsR (PowerSeries ℂ) ⟶ W.t.G), (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ i) ∧ IsLieBasis v' := by
  intro E _ _ _ H Dw l Xo c σ V Y a χ W M hM
  have cast : ∀ (p q : Sp (PowerSeries ℂ) ⟶ Y.X) (_ : p = q) (n : SABMap W.t Y.t p),
      ∃ n' : SABMap W.t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ (spMap (ev χ M.U hM) ≫ M.hU.fromSpec) (GlobalTheory.FlagMod.spMap_ev χ M.hU hM).symm W.m
  obtain ⟨v', hv', hb, -⟩ := M.lie (PowerSeries ℂ) (ev χ M.U hM) W.t m'
  refine ⟨v', fun j => ?_, hb⟩
  rw [← hm', hv' j]
  have e : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev χ M.U hM) = dualMap (ev χ M.U hM) := by
    ext x <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, dualMap]
  rw [e]

theorem exists_lieComb_matrix : ∀ (R : Type) [CommRing R] [Nontrivial R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n n' : ℕ) (v : Fin n → (epsR R ⟶ G)) (v' : Fin n' → (epsR R ⟶ G)), IsLieBasis v → IsLieBasis v' → ∃ h : n' = n, ∃ A : Matrix (Fin n) (Fin n) R, IsUnit A.det ∧ ∀ i, IsLieComb (A i) v (v' (Fin.cast h.symm i)) := by
  intro R _ _ G _ _ O _ act n n' v v' hv hv'
  let b := GlobalTheory.Serre.Lie.basis act hv
  let b' := GlobalTheory.Serre.Lie.basis act hv'
  have h : n' = n := by simpa using Fintype.card_congr (b'.indexEquiv b)
  subst h
  refine ⟨rfl, (b.toMatrix b').transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose]
    refine IsUnit.of_mul_eq_one (b'.toMatrix b).det ?_
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  · have hv_eq : v = fun k => (b k).hom := funext fun k => (GlobalTheory.Serre.Lie.hom_basis (a := act) hv k).symm
    rw [Fin.cast_eq_self, ← GlobalTheory.Serre.Lie.hom_basis (a := act) hv' i, hv_eq, GlobalTheory.Serre.Lie.isLieComb_iff]
    congr 1
    conv_lhs => rw [← b.sum_repr (b' i)]
    rfl

theorem lieCoord_det_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M h1 h2 h3 h4 h5 h6
  obtain ⟨e, v, z, hev, hv, hz⟩ := _root_.GlobalTheory.ArcLieFrame.exists_const_frame E H Dw l Xo c σ V Y a χ W g ty Fu Ha
  obtain ⟨v', hv'1, hv'2⟩ := exists_chartLie_along E H Dw l Xo c σ V Y a χ W M h6
  obtain ⟨hn, A, hA, hAc⟩ := exists_lieComb_matrix (PowerSeries ℂ) W.t.G (𝓞 E) W.t.act g M.n v v' hv hv'2
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.T.arc_lieBasis_exponentialCoords_hasSum E H Dw l Xo c σ V Y a χ W g ty Fu Ha M h6 e v z hn (fun i => v' (Fin.cast hn.symm i)) A
    h1 h2 h3 h4 h5 hev hv hz (fun i => hv'1 _) hAc
  by_cases hex : ∃ w : ℂ, T₀ < w.im ∧ ∀ i k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)
  swap
  · refine ⟨T₀, 1, one_pos, ?_⟩
    intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
    exact (hex ⟨w, hw, fun i k => (hT₀ w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf i).1 k⟩).elim
  obtain ⟨w₀, -, hs⟩ := hex
  obtain ⟨T', C, hC, hb⟩ := _root_.GlobalTheory.det_bounded_eTwoPi g A w₀ hA hs
  have hd : 0 < ‖(Matrix.of z).det‖ := norm_pos_iff.2 hz
  refine ⟨max T₀ T', C * (‖(Matrix.of z).det‖ + ‖(Matrix.of z).det‖⁻¹), by positivity, ?_⟩
  intro w hw yF e1 e2 hz' x φ hk hg u Wv hf hdf
  have hM : (Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j) =
      (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m) * Matrix.of z := by
    ext i j
    rw [Matrix.of_apply, ((hT₀ w (lt_of_le_of_lt (le_max_left _ _) hw) yF e1 e2 hz' x φ hk hg u Wv hf hdf i).2 j),
      Matrix.mul_apply]
    rfl
  rw [hM, Matrix.det_mul, norm_mul]
  obtain ⟨b1, b2⟩ := hb w (lt_of_le_of_lt (le_max_right _ _) hw)
  set d := ‖(Matrix.of z).det‖
  set t := ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖
  constructor
  · rw [mul_inv, ← div_eq_mul_inv]
    calc C⁻¹ / (d + d⁻¹) ≤ C⁻¹ * d := by
          rw [div_le_iff₀ (by positivity)]
          have : 1 ≤ d * (d + d⁻¹) := by rw [mul_add, mul_inv_cancel₀ hd.ne']; nlinarith
          nlinarith [inv_pos.2 hC]
      _ ≤ t * d := mul_le_mul_of_nonneg_right b1 hd.le
  · calc t * d ≤ C * d := mul_le_mul_of_nonneg_right b2 hd.le
      _ ≤ C * (d + d⁻¹) := by nlinarith [inv_pos.2 hd]

end GlobalTheory.ArcNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide

section Clauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HeckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (hL j k P x)) =
      hkNorm R (idxOf D j) k P • heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))

def LvlPsi (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  (∀ g : G, g ∈ F.P0 ↔ (R.eG.trans cG) g ∈ Formalism.IndefR.NX.U D.nd) ∧
    ∀ (u : F.P0) (hu : (R.eG.trans cG) u ∈ Formalism.IndefR.NX.U D.nd),
      (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = (((F.ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)

end Clauses

section Rat

variable {D : D7}

def FormsC (S : RatDat D.ntw) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm ∧ FiniteDimensional S.Ks (FmK S j) ∧
    ∃ T : Finset (S.WL j), (∀ x ∈ T, x ∈ (S.A j).MK) ∧
      (∀ x ∈ (S.A j).MK, x ∈ (S.A j).WK ∧ x ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j))) ∧
      ∀ x ∈ (S.A j).WK, x ∈ Submodule.span S.Ks (T : Set (S.WL j))

def StabC (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK

def IntC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) : Prop :=
  ∀ j k P, 1 ≤ j → j ≤ D.R.m → IsSplitPl D.host P → P ∉ Sb → k ≤ D.R.r → ∃ n : ℕ,
    ∀ x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), x ∈ goodL D S θ j →
      (normV P) ^ n • hL j k P x ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j))

def SpanC (S : RatDat D.ntw) (Sb : Finset (PlE D.host)) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → goodL D S θ j ≤
    ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D S θ j ⊓ ⨅ (k : ℕ) (P : PlE D.host)
      (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb), Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL)

def lowSet (D : D7) : Set (PlE D.host) := {v | ∃ p ∈ lowAll D, p ≠ 0 ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}

theorem lowSet_finite (D : D7) : (lowSet D).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion (s := (((lowAll D).filter (· ≠ 0) : Finset ℕ) : Set ℕ)) (Finset.finite_toSet _)
    fun p hp => GlobalTheory.RowTie.placesOver_finite_of_ne_zero D.host.E p (Finset.mem_filter.1 hp).2) ?_
  rintro v ⟨p, hp, hp0, hv⟩
  exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hp, hp0⟩)) hv

def SbD (D : D7) : Finset (PlE D.host) := (lowSet_finite D).toFinset

theorem overSet_SbD (D : D7) : OverSet D (SbD D) (lowAll D) := by
  intro v hv
  obtain ⟨p, hp, -, hv⟩ := (lowSet_finite D).mem_toFinset.1 hv
  exact ⟨p, hp, hv⟩

end Rat

section State

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def kKsOf (x : St P) : x.m.z.core.Q.c.F →+* ↥(Dof x).LL0 :=
  (algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL).codRestrict (Dof x).LL0 x.m.z.fieldValues_mem_fixedField

theorem hkOf (x : St P) (y : x.m.z.core.Q.c.F) :
    ((kKsOf x y : ↥(Dof x).LL0) : (Dof x).what₂.LL) = algebraMap x.m.z.core.Q.c.F (Dof x).what₂.LL y := rfl

abbrev SOf (x : St P) : RatDat (Dof x).ntw := ratDatR x.m.z.R x.m.z.cG (kKsOf x) (hkOf x)

end State

end GlobalTheory.HeightCounting.RatSide
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace Mark

section Defs

variable {O : Type} [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

def InFace (β x : LinearMap.BilinForm ℤ X) : Prop :=
  x ∈ balForms bar X ∧ (∀ y, 0 ≤ x y y) ∧ (∀ y, β y y = 0 → x y y = 0) ∧
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x ∧ lab.evalZ (β + x) = lab.evalZ β

def IsIndec (β x : LinearMap.BilinForm ℤ X) : Prop :=
  InFace bar ψ lab β x ∧ x ≠ 0 ∧ ∀ y z, InFace bar ψ lab β y → InFace bar ψ lab β z → y ≠ 0 → z ≠ 0 → y + z ≠ x

variable (X) in
def IsMarked (β : LinearMap.BilinForm ℤ X) : Prop :=
  β ∈ balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧
    lab.evalZ β = ((i + 1 : ℕ) : ℝ) ∧
    ∃ S : Finset (LinearMap.BilinForm ℤ X), (∀ x, x ∈ S ↔ IsIndec bar ψ lab β x) ∧
      ∃ k : ℕ, 0 < k ∧ (k : ℤ) • β = ∑ x ∈ S, x

open Classical in
def markVal (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : ℝ :=
  if h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B a b = β a b then
    (if IsMarked bar ψ lab i (Fin n → O) h.choose then 1 else 0) else 0

end Defs

section Basic

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

open Classical in
theorem markVal_int (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    markVal bar ψ lab i n (fun a b => (β a b : ℝ)) = if IsMarked bar ψ lab i (Fin n → O) β then 1 else 0 := by
  classical
  unfold markVal
  have h : ∃ β' : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, ((β a b : ℤ) : ℝ) = β' a b := ⟨β, fun _ _ => rfl⟩
  rw [dite_eq_left h]
  have e : h.choose = β := LinearMap.ext₂ fun a b => by
    have := h.choose_spec a b
    exact_mod_cast this.symm
  rw [e]

end Basic

end Mark

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealOfFlatStalkPullback
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlatPush

theorem flat_sections_to_chart {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens)
    (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (hx : ξ (closedPoint R) ∈ (U : X.Opens)) (hfl : (Scheme.stalkClosedPointTo ξ).hom.Flat) :
    (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.Flat := by
  have hf : (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) =
      X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo ξ := by
    rw [Scheme.germ_stalkClosedPointTo]; rfl
  rw [hf, CommRingCat.hom_comp]
  refine RingHom.Flat.comp ?_ hfl
  letI : Algebra Γ(X, U) (X.presheaf.stalk (ξ (closedPoint R))) := X.presheaf.algebra_section_stalk ⟨_, hx⟩
  haveI := U.2.isLocalization_stalk ⟨_, hx⟩
  have : Module.Flat Γ(X, U) (X.presheaf.stalk (ξ (closedPoint R))) := IsLocalization.flat _ (U.2.primeIdealOf ⟨_, hx⟩).asIdeal.primeCompl
  exact this

theorem tmul_mem_of_germ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) (I : Y'.IdealSheafData) {R : Type} [CommRing R]
    (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens)
    (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)) (h : R)
    (hh : ∀ v : ↥(pullback ξ ρ : Scheme.{0}), ((pullback ξ ρ).presheaf.germ ⊤ v trivial).hom
      ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h)) ∈
        FinalTheorems.stalkId (I.comap (pullback.snd ξ ρ)) v) :
    letI := (ρ.appLE U W hW).hom.toAlgebra
    letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
    (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] h ∈ (I.ideal W).map
      (Algebra.TensorProduct.includeLeftRingHom : Γ(Y', W) →+* Γ(Y', W) ⊗[Γ(X, U)] R) := by
  letI := (ρ.appLE U W hW).hom.toAlgebra
  letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  obtain ⟨κ, hκ, hL, hR⟩ := GlobalTheory.T.exists_specTensor_to_pullback_sections_compat ρ ξ U hle W hW
  obtain ⟨s0, hs0⟩ : ∃ s0, (pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h) = s0 :=
    ⟨_, rfl⟩
  rw [hs0] at hh
  have hs : ∀ t, ((Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).presheaf.germ ⊤ t trivial).hom
      (κ.appTop.hom s0) ∈ FinalTheorems.stalkId (I.comap (κ ≫ pullback.snd ξ ρ)) t := by
    intro t
    have e := Scheme.Hom.germ_stalkMap_apply κ ⊤ t trivial s0
    rw [Scheme.IdealSheafData.comap_comp]
    refine GlobalTheory.VanStalk.map_le_stalkId_comap κ _ t ?_
    have : (κ.stalkMap t).hom (((pullback ξ ρ).presheaf.germ ⊤ (κ t) trivial).hom s0) ∈ _ :=
      Ideal.mem_map_of_mem _ (hh (κ t))
    rw [e] at this
    exact this
  have h4 := _root_.GlobalTheory.GermAff.mem_map_of_germ (κ ≫ pullback.snd ξ ρ) I W hκ _ hs
  have h5 := Ideal.mem_map_of_mem (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).hom.hom h4
  rw [Ideal.map_map] at h5
  have e1 : (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom s0) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] h := by
    rw [← hR h, ← hs0]
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R))).hom.hom.comp
      ((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom = Algebra.TensorProduct.includeLeftRingHom := by
    ext c; exact hL c
  rwa [e1, e2] at h5

theorem mem_idlAlong_map_of_flat : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] [QuasiSeparated ρ]
    (I : Y'.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X),
    (Scheme.stalkClosedPointTo ξ).hom.Flat → ∀ h : R, (∀ v : ↥(pullback ξ ρ : Scheme.{0}),
      ((pullback ξ ρ).presheaf.germ ⊤ v trivial).hom ((pullback.fst ξ ρ).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h)) ∈ FinalTheorems.stalkId (I.comap (pullback.snd ξ ρ)) v) →
      h ∈ idlAlong (I.map ρ) ξ := by
  intro X Y' ρ _ _ I R _ _ ξ hfl h hh
  obtain ⟨U₀, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  let U : X.affineOpens := ⟨U₀, hU⟩
  have hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens) := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
  have he : idlAlong (I.map ρ) ξ = ((I.map ρ).ideal U).map
      (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    unfold idlAlong
    rw [ds_stalkId_eq_map (I.map ρ) U _ hx, Ideal.map_map,
      ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  rw [he]
  have hc : IsCompact ((ρ ⁻¹ᵁ (U : X.Opens) : Y'.Opens) : Set Y') :=
    QuasiCompact.isCompact_preimage (f := ρ) _ U.1.isOpen U.2.isCompact
  obtain ⟨Us, hUs, hfin, heq⟩ := Y'.isBasis_affineOpens.exists_finite_of_isCompact hc
  let ι := ↥Us
  haveI : Finite ι := hfin.to_subtype
  let W : ι → Y'.affineOpens := fun i => ⟨i.1, hUs i.2⟩
  have hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens) := fun i => heq ▸ le_sSup i.2
  have hcov : ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens) := by
    rw [heq, sSup_le_iff]
    intro V hV
    exact le_iSup (fun i : ι => (W i : Y'.Opens)) ⟨V, hV⟩
  letI : Algebra Γ(X, U) R := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  haveI : Module.Flat Γ(X, U) R := GlobalTheory.FlatPush.flat_sections_to_chart ξ U hle hx hfl
  let K : ι → Ideal Γ(X, U) := fun i => (I.ideal (W i)).comap (ρ.appLE U (W i) (hW i)).hom
  have h1 : ⨅ i, K i ≤ (I.map ρ).ideal U := fun b hb =>
    _root_.GlobalTheory.IdealPushCover.mem_map_ideal_of_cover ρ I U W hW hcov b fun i => (Ideal.mem_iInf.1 hb i)
  have h2 : h ∈ ⨅ i, (K i).map (algebraMap Γ(X, U) R) := by
    refine Ideal.mem_iInf.2 fun i => ?_
    letI : Algebra Γ(X, U) Γ(Y', W i) := (ρ.appLE U (W i) (hW i)).hom.toAlgebra
    exact GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map (I.ideal (W i)) h (tmul_mem_of_germ ρ I ξ U hle (W i) (hW i) h hh)
  exact Ideal.map_mono h1 (_root_.GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf K h2)

end GlobalTheory.FlatPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
section
noncomputable section

open MvPolynomial Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder

namespace GlobalTheory.PointChern

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def coordOf {H : Host E} {Dw : Datum H} {n : ℕ} (e : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (w : ReciprocityTheory.L2DbarEstimates.V n) : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ :=
  fun τ i j => w (e.symm (τ, i, j))

def InDom {H : Host E} {Dw : Datum H} (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) : Prop :=
  ∀ τ, (1 - (z τ)ᴴ * z τ).PosDef

theorem mult_of_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : Dw.mult τ = Dw.p := by
  simp [Datum.mult, h]

theorem mult_of_not_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    Dw.mult τ = Dw.q := by
  simp [Datum.mult, h]


open Classical in
def modelGram (H : Host E) (Dw : Datum H) (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) :
    GlobalTheory.FlagBundle.Mat Dw.mult ℂ := fun τ =>
  if h : τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
      (1 - (z ⟨τ, h⟩).map (starRingEnd ℂ) * (z ⟨τ, h⟩)ᵀ)⁻¹
  else if h' : conjEmb τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
      (1 - (z ⟨conjEmb τ, h'⟩)ᴴ * z ⟨conjEmb τ, h'⟩)⁻¹
  else 1

def relPoly {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  ∑ a ∈ Finset.range (k + 1), C ((-1 : ℝ) ^ (k - a)) * X (τ.1, a) * X (conjEmb τ.1, k - a)

end GlobalTheory.PointChern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesLieCoordinatesUnitary
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

theorem lie_coord_unitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x x₁ : (U.X k).dom), IsOrth (U.X k) x.1 → IsOrth (U.X k) x₁.1 → (U.un k x₁).x = (U.un k x).x → ∀ (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), (∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (T b' b : ℂ)) ((U.un k x₁).u τ b)) → Tᴴ * T = 1 := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x x₁ hx hx₁ e τ T hT
  obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r _ hU
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.HodgeSmooth.exists_diag_riem hσ hU W
  obtain ⟨Hm, -, -, hH⟩ := (W.period k x₁).2.2.2.2
  obtain ⟨hPx, hv⟩ := W.lie k x₁
  have h1 := hd k x₁ hx₁ (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH hPx.symm τ _ ((U.un k x₁).u τ) 1 (hv τ)
    (fun b => by
      convert GlobalTheory.isCombAt_single_of_isTanAt (U.un k x₁).x ((U.un k x₁).u τ) ((U.un k x₁).tan τ) b using 1
      show (fun b' => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) b' b) = Pi.single b 1
      funext b'
      rw [Matrix.one_apply, Pi.single_apply])
  have h2 := hd k x hx (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH (hPx.symm.trans e) τ _ ((U.un k x₁).u τ) T
    (hv τ) hT
  have h3 : d k τ • (Tᴴ * T) = d k τ • (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) := by
    rw [← h2, h1, conjTranspose_one, Matrix.mul_one]
  exact smul_right_injective _ (hd0 k τ) h3

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesServedPlaceEqLocalOrbitPairsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroClasses_servedPlace_eq_localOrbitPairs : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ cls0 : ((w.D Z).gat u v hg).comp → ((w.D Z).gat u v hg).P.Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls 0,
        (∀ (a a' : ((w.D Z).gat u v hg).comp) (L L' : ((w.D Z).gat u v hg).P.Tup), ((w.D Z).gat u v hg).P.IsLatTup L →
          ((w.D Z).gat u v hg).P.IsLatTup L' →
          (cls0 a L = cls0 a' L' ↔ a = a' ∧ ∃ γ : (((w.D Z).gat u v hg).lev a).Γ, L' = (((w.D Z).gat u v hg).lev a).smul γ L)) ∧
        ∀ x, ∃ a L, ((w.D Z).gat u v hg).P.IsLatTup L ∧ cls0 a L = x := by
  first | exact @GlobalTheory.Mem.Top.KerOne.stepZeroClasses_servedPlace_eq_localOrbitPairs_alt | exact GlobalTheory.Mem.Top.KerOne.stepZeroClasses_servedPlace_eq_localOrbitPairs_alt | (intros; apply GlobalTheory.Mem.Top.KerOne.stepZeroClasses_servedPlace_eq_localOrbitPairs_alt <;> assumption)
end

