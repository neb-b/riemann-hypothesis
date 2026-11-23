module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0219
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0228
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0234
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0229
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0244
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftLocalPositiveCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0245
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0100
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0180
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0144
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfLeaves
section
namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField

noncomputable section

theorem waveLocB_of_cpt (hPSC : P5.ThmPActualCpt → StandardPairingDecay.PStdC) : P5.ThmPActualCpt → WaveLocB := by
  intro hA Cb
  refine ⟨28 * Real.exp 1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB
  exact wave_local_positive_compact_support hA (hPSC hA) Cb _ E Wp Wq S p f χ A₀ le_rfl hB

theorem liftLocB_of_cpt (hDL : KB.DegLift) : P5.ThmPActualCpt → LiftLocB := by
  intro hA Cb
  refine ⟨28 * Real.exp 1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB
  obtain ⟨Λ0, hΛ0, hl⟩ := lift_local_positive_compact_support hA hDL Cb _ E Wp Wq S p f χ A₀ le_rfl hB
  refine ⟨fun b s v => if 1 ≤ b ∧ 1 ≤ s ∧ b + s ≤ S.G.r + 1 then Λ0 b s v else 0, ?_, ?_, ?_⟩
  · intro b s v
    beta_reduce
    by_cases h : 1 ≤ b ∧ 1 ≤ s ∧ b + s ≤ S.G.r + 1
    · rw [if_pos h]; exact (hΛ0 b s h.1 h.2.1 h.2.2 v).1
    · rw [if_neg h]
  · intro b s hb hs hbs v
    beta_reduce
    rw [if_pos ⟨hb, hs, hbs⟩]; exact (hΛ0 b s hb hs hbs v).2
  · intro F hF v b s hb hs hbs
    have h : (if 1 ≤ b ∧ 1 ≤ s ∧ b + s ≤ S.G.r + 1 then Λ0 b s v else 0) = Λ0 b s v := if_pos ⟨hb, hs, hbs⟩
    simp only [h]
    exact hl F hF v b s hb hs hbs

end

def BuiltBounds2CptOfLeaves : Prop :=
  KB.RadHead → KB.HeadTop → KB.DegLift → PBL.TopLocB → KB.DegTop → PBL.TopRatio → GermPartsC →
  (P5.ThmPActualCpt → DecayUnif) → KB.BuiltBounds2Cpt

theorem builtBounds2CptOfLeaves : BuiltBounds2CptOfLeaves := by
  intro hRH hHT hDL hTL hDT hTR hGP hD
  have hPSC : P5.ThmPActualCpt → StandardPairingDecay.PStdC := fun hA => StandardPairingDecay.pStdC_of hA hRH hHT
  have hI : P5.ThmPActualCpt → IntB := fun hA => integral_bound_of_parts (hPSC hA) (hD hA)
  exact builtBounds2CptOfParts (waveLocB_of_cpt hPSC) (liftLocB_of_cpt hDL) hTL (fun _ => hDT)
    (fun _ => vector_valued_types) (fun _ => hTR) (fun hA => germLocB_of (hI hA) hGP) positivity_bound hI hD
    (fun _ => thrPos)

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact_of_leaves : PBASM.BuiltBounds2CptOfLeaves := PBASM.builtBounds2CptOfLeaves

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContDiffOnInvConjDet
section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def TopG {ι X : Type} [DecidableEq ι] (Eop : ι → ι → (X → E) → (X → E)) (u : ℂ) (a b : ι) (f : X → E) : X → E :=
  fun g => (if a = b then u • f g else 0) + Eop a b f g

def qminG {ι X : Type} [DecidableEq ι] {t : ℕ} (Eop : ι → ι → (X → E) → (X → E)) (a b : Fin t → ι) (u : ℂ)
    (f : X → E) : X → E :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin t => TopG Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) f)

def EopZ (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : (MJ j → E) → MJ j → E :=
  if hp : p.val < j then (if hq : q.val < j then EZ ⟨p.val, hp⟩ ⟨q.val, hq⟩ else fun _ _ => 0)
  else if hp' : 2 * r + k < p.val + j then
    (if hq' : 2 * r + k < q.val + j then
      EZs ⟨2 * r + k - p.val, by omega⟩ ⟨2 * r + k - q.val, by omega⟩ else fun _ _ => 0)
  else fun _ _ => 0

def cZ {j N : ℕ} (Z : MJ j) (p : Fin N) (a : Fin j) : ℂ := if hp : p.val < j then Z a ⟨p.val, hp⟩ else 0

def cvZ (k r : ℕ) {j : ℕ} (Z : MJ j) (p : Fin (2 * r + k + 1)) (a : Fin j) : ℂ :=
  if hp : 2 * r + k < p.val + j then conj (Z a ⟨2 * r + k - p.val, by omega⟩) else 0


open scoped Classical in
def AZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ) (h : MJ j → E) : MJ j → E := fun Z =>
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m => cZ Z (c l) (Fin.castLE hmj a)).det •
        qminG (EopZ (E := E) k r j) (C3.xR k r m hm) c u h Z
    else 0


open scoped Classical in
def AvZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (ell : ℂ) (h : MJ j → E) : MJ j → E := fun Z =>
  ∑ B : Fin m → Fin (2 * r + k + 1),
    if StrictMono (fun l => C3.keyS k r (B l)) then
      (Matrix.of fun a l : Fin m => cvZ k r Z (B l) (Fin.castLE hmj a)).det •
        qminG (EopZ (E := E) k r j) B (C3.sR k r m hm) (ell + (m : ℂ) - 1) h Z
    else 0

def Aform (k r j : ℕ) (hj : j + 1 ≤ r) (l : C.Letter) (e : Fin 2) (h : MJ j → E) : MJ j → E := fun Z =>
  if e = 1 ∧ j = 0 then 0 else
  if l.1 then
    (Z.det)⁻¹ • AZ k r j (j - e) (by omega) (by omega) ((l.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) h Z
  else
    (conj Z.det)⁻¹ • AvZ k r j (j - e) (by omega) (by omega) ((l.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) h Z

section zop

variable (hR : ZOpRd)
include hR

theorem zop_EZ {j : ℕ} (a b : Fin j) : ZOp (E := E) (EZ a b) :=
  (hR j E _).add' ((hR j E _).csmul Complex.I)

theorem zop_EZs {j : ℕ} (a b : Fin j) : ZOp (E := E) (EZs a b) :=
  (hR j E _).add' ((hR j E _).csmul Complex.I)

theorem zop_EopZ (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : ZOp (E := E) (EopZ k r j p q) := by
  unfold EopZ
  split_ifs
  · exact zop_EZ hR _ _
  · exact zop_zero
  · exact zop_EZs hR _ _
  · exact zop_zero
  · exact zop_zero

theorem zop_TopG (k r j : ℕ) (u : ℂ) (p q : Fin (2 * r + k + 1)) :
    ZOp (E := E) (TopG (EopZ k r j) u p q) := by
  have h1 : ZOp (E := E) (j := j) (fun f g => if p = q then u • f g else 0) := by
    split_ifs
    · exact zop_id.csmul u
    · exact zop_zero
  exact h1.add' (zop_EopZ hR k r j p q)

theorem zop_qminG (k r j : ℕ) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    ZOp (E := E) (qminG (EopZ k r j) a b u) := by
  have e : (qminG (E := E) (EopZ k r j) a b u) = fun h Z => ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin t))),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun k' : Fin t =>
        TopG (EopZ (E := E) k r j) (u - ((k' : ℕ) : ℂ)) (a (σ k')) (b k')).foldr (fun T h => T h) h Z) := by
    funext h Z
    simp [qminG, Finset.sum_apply]
  rw [e]
  refine zop_sum _ (fun σ _ => ?_)
  refine ZOp.csmul ?_ _
  refine zop_foldr _ (fun T hT => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  exact zop_TopG hR k r j _ _ _

end zop

theorem contDiff_entry {j : ℕ} (a b : Fin j) : ContDiff ℝ ∞ fun Z : MJ j => Z a b :=
  (contDiff_apply ℝ (fun _ => ℂ) b).comp (contDiff_apply ℝ (fun _ => (Fin j → ℂ)) a)

theorem contDiff_det_of {j m : ℕ} (M : MJ j → Matrix (Fin m) (Fin m) ℂ) (hM : ∀ a b, ContDiff ℝ ∞ fun Z => M Z a b) :
    ContDiff ℝ ∞ fun Z => (M Z).det := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum (fun σ _ => ?_)
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod (fun i _ => hM _ _))

theorem contDiff_cZ {j N : ℕ} (p : Fin N) (a : Fin j) : ContDiff ℝ ∞ fun Z : MJ j => cZ Z p a := by
  unfold cZ
  split_ifs
  · exact contDiff_entry _ _
  · exact contDiff_const

theorem contDiff_cvZ (k r : ℕ) {j : ℕ} (p : Fin (2 * r + k + 1)) (a : Fin j) :
    ContDiff ℝ ∞ fun Z : MJ j => cvZ k r Z p a := by
  unfold cvZ
  split_ifs
  · exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)
  · exact contDiff_const

theorem contDiffOn_invDet {j : ℕ} : ContDiffOn ℝ ∞ (fun Z : MJ j => (Z.det)⁻¹) {Z | Z.det ≠ 0} :=
  (contDiff_det_of (fun Z => Z) (fun a b => contDiff_entry a b)).contDiffOn.inv (fun Z hZ => hZ)

theorem contDiffOn_invConjDet {j : ℕ} :
    ContDiffOn ℝ ∞ (fun Z : MJ j => (conj Z.det)⁻¹) {Z | Z.det ≠ 0} :=
  (Complex.conjCLE.contDiff.comp (contDiff_det_of (fun Z => Z) (fun a b => contDiff_entry a b))).contDiffOn.inv
    (fun Z hZ => by simpa using hZ)

section zop2

variable (hR : ZOpRd)
include hR

theorem zop_AZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ) : ZOp (E := E) (AZ k r j m hm hmj u) := by
  classical
  unfold AZ
  refine zop_sum _ (fun c _ => ?_)
  split_ifs
  · exact (zop_qminG hR k r j _ _ u).cmul
      (contDiff_det_of _ (fun a l => contDiff_cZ _ _)).contDiffOn
  · exact zop_zero

theorem zop_AvZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (ell : ℂ) : ZOp (E := E) (AvZ k r j m hm hmj ell) := by
  classical
  unfold AvZ
  refine zop_sum _ (fun c _ => ?_)
  split_ifs
  · exact (zop_qminG hR k r j _ _ _).cmul
      (contDiff_det_of _ (fun a l => contDiff_cvZ k r _ _)).contDiffOn
  · exact zop_zero

theorem zop_Aform (k r j : ℕ) (hj : j + 1 ≤ r) (l : C.Letter) (e : Fin 2) :
    ZOp (E := E) (Aform k r j hj l e) := by
  unfold Aform
  split_ifs
  · exact zop_zero
  · exact (zop_AZ hR _ _ _ _ _ _ _).cmul contDiffOn_invDet
  · exact (zop_AvZ hR _ _ _ _ _ _ _).cmul contDiffOn_invConjDet

end zop2
end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkCpt
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkCptPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section casts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def castBS {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : B.RealPlaceData k b Wp Wq := e ▸ Bs

theorem castBS_z_eq_castV {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : (castBS e Bs).z = D.castV e Bs.z := by
  subst e
  rfl

theorem castBS_z'_eq_castV {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : (castBS e Bs).z' = D.castV e Bs.z' := by
  subst e
  rfl

theorem cptCoef_castF {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) (G : B.Mat k b → (Wq →L[ℂ] Wp))
    (h : KB.CptCoef (castBS e Bs) G) : KB.CptCoef Bs (D.castF e G) := by
  subst e
  exact h

end casts

theorem glev_last_iff {k ρ : ℕ} (hρ : ρ = 0) (g : B.Mat k ρ) :
    g ∈ Q.Glev k ρ (Fin.last ρ) ↔ g ∈ B.GV k ρ := by
  subst hρ
  exact Formalism.FourierDecayAlt.P.JCx2.sq_glev0 g

theorem gf_eq_ggl {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) :
    Gf k ρ z z' g = Q.GGl k ρ z z' g := by
  subst hρ
  have h0 : Dmin k 0 z z' g ⟨0, by omega⟩ = 1 := by
    unfold Dmin
    exact Matrix.det_isEmpty
  have h1 : Dmin k 0 z z' g (Fin.last 1) = Zhat k 0 z z' g (Fin.last 0) (Fin.last 0) := by
    unfold Dmin
    exact Matrix.det_fin_one _
  unfold Gf Q.GGl
  rw [Formalism.FourierDecayAlt.P.PBI.zetaL_eq_zhat, h0, h1]
  simp

end Formalism.FourierDecayAlt.P.CutEX.MkCptPf

namespace Formalism.FourierDecayAlt.P.CutEX.MkCptPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem lowV_top {k r : ℕ} (T : D.LevTower k r Wp Wq) (e : r = r + (r - r)) :
    U.lowV k r (r - r) (D.castV e T.base.z) = (T.bs r).z := by
  have hzl := (T.z_lev r le_rfl).symm
  change T.base.z = _ at hzl
  rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
  exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _

theorem lowV_top' {k r : ℕ} (T : D.LevTower k r Wp Wq) (e : r = r + (r - r)) :
    U.lowV k r (r - r) (D.castV e T.base.z') = (T.bs r).z' := by
  have hzl := (T.z'_lev r le_rfl).symm
  change T.base.z' = _ at hzl
  rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
  exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _

end top

theorem mkCpt : MkCpt := by
  intro Wp Wq _ _ _ _ _ _ P p b b' hb hbc hb' hb'c Φ hΦ K hK hKU hsupp
  have hρ : P.r - P.r = 0 := Nat.sub_self _
  have e : P.r = P.r + (P.r - P.r) := by omega
  have hz : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z = (p.T.bs P.r).z := by
    rw [castBS_z_eq_castV]; exact lowV_top p.T e
  have hz' : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z' = (p.T.bs P.r).z' := by
    rw [castBS_z'_eq_castV]; exact lowV_top' p.T e
  have hUTo : IsOpen (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') := by
    have c1 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) :=
      Continuous.matrix_det continuous_fst
    have c2 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) =>
        Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of q.2)) :=
      (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous _ _ _ _).comp continuous_snd
    exact (isOpen_ne_fun c1 continuous_const).inter (isOpen_lt continuous_const c2)
  have hCpt : KB.CptCoef (castBS e p.T.base) (PBI.chartCoefficient b b' Φ) := by
    refine PBI.chartCoefficient_hasCompactSupport (castBS e p.T.base) b b' hb hbc hb' hb'c Φ (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')
      hUTo ?_ K hK hKU ?_ ?_
    · intro q₀ hq₀ hG
      obtain ⟨U', F, hU', hq, hF, hEq⟩ := hΦ q₀ hq₀ ((glev_last_iff hρ _).2 hG)
      exact ⟨U', F, hU', hq, hF, fun q hqU hqG => hEq q hqU ((glev_last_iff hρ _).2 hqG)⟩
    · intro q hq
      obtain ⟨h1, h2⟩ := hKU hq
      refine ⟨h1, ?_⟩
      rw [hz, hz', gf_eq_ggl hρ]
      exact h2
    · intro q hG hq
      exact hsupp q ((glev_last_iff hρ _).2 hG) hq
  refine ⟨cptCoef_castF e p.T.base _ hCpt,
    (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) '' K,
    hK.image (Continuous.matrix_det continuous_fst), ?_, ?_⟩
  · rintro ⟨q, hq, h0⟩
    exact (hKU hq).1 h0
  · intro g hg hne
    have hg' : D.castM e g ∈ B.GV P.k (P.r + (P.r - P.r)) := Formalism.FourierDecayAlt.P.PBE.castM_GV e hg
    have hne' : PBI.chartCoefficient b b' Φ (D.castM e g) ≠ 0 := hne
    have hD : U.DjU P.k P.r (P.r - P.r) (D.castM e g) ≠ 0 := by
      intro h0; apply hne'; unfold PBI.chartCoefficient; rw [if_neg (not_not.2 h0)]
    obtain ⟨-, hμ, heq⟩ := PBI.chart_spec (D.castM e g) hg' hD
    have hmk := hne'
    unfold PBI.chartCoefficient at hmk
    rw [if_pos hD] at hmk
    obtain ⟨-, hΦne⟩ := smul_ne_zero_iff.1 hmk
    have hμ' : Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.2 ∈ B.GV P.k (P.r - P.r) := by
      simpa only [PBI.chart, Equiv.apply_symm_apply] using hμ
    have hK' : (PBI.chart (Matrix.of.symm (D.castM e g))).2 ∈ K := by
      by_contra hn
      exact hΦne (hsupp _ ((glev_last_iff hρ _).2 hμ') hn)
    refine ⟨_, hK', ?_⟩
    have hpsi : PBI.psiC (PBI.chart (Matrix.of.symm (D.castM e g))) = D.castM e g := by
      unfold PBI.psiC PBI.chart
      simp only [Equiv.apply_symm_apply]
      exact heq.symm
    have e1 := PBI.djU_psiC (PBI.chart (Matrix.of.symm (D.castM e g)))
    rw [hpsi] at e1
    show (Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.1).det = _
    rw [← e1, ← Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r) (D.castV e p.T.base.z) (D.castV e p.T.base.z'),
      Formalism.FourierDecayAlt.P.PBG.Dmin_castM e _ _ g P.r, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV,
      Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self]

end Formalism.FourierDecayAlt.P.CutEX.MkCptPf

namespace Formalism.FourierDecayAlt.P

theorem compact_truncation_construction : CutEX.MkCpt := CutEX.MkCptPf.mkCpt

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopBump
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkTopBump

theorem bump_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (f g : E → ℂ) (hf : Continuous f) (hg : Continuous g) (hf0 : f 0 = 1) (hg0 : g 0 = 1) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ (∫ x, (b x : ℂ) * f x ∂μ) ≠ 0 ∧
      (∫ x, (b x : ℂ) * g x ∂μ) ≠ 0 := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hf.continuousAt (1 / 2 : ℝ) (by norm_num)
  obtain ⟨δ', hδ', hδg⟩ := Metric.continuousAt_iff.1 hg.continuousAt (1 / 2 : ℝ) (by norm_num)
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  let B : ContDiffBump (0 : E) := ⟨min δ δ' / 4, min δ δ' / 2, by positivity, by linarith⟩
  set b : E → ℝ := fun x => B x with hbdef
  have hbd : ContDiff ℝ ∞ b := B.contDiff
  have hbc : HasCompactSupport b := B.hasCompactSupport
  have hbnn : ∀ x, 0 ≤ b x := fun x => B.nonneg
  have hbcont : Continuous b := B.continuous
  have hbint : 0 < ∫ x, b x ∂μ := B.integral_pos
  have hbs : tsupport b ⊆ Metric.ball (0 : E) (min δ δ') := by
    rw [show tsupport b = Metric.closedBall (0 : E) (min δ δ' / 2) from B.tsupport_eq]
    exact Metric.closedBall_subset_ball (by linarith)
  have aux : ∀ h : E → ℂ, Continuous h →
      (∀ x, dist x 0 < min δ δ' → ‖h x - 1‖ < 1 / 2) → (∫ x, (b x : ℂ) * h x ∂μ) ≠ 0 := by
    intro h hh hs
    have hbC : Continuous (fun x => (b x : ℂ)) := Complex.continuous_ofReal.comp hbcont
    have hbcC : HasCompactSupport (fun x => (b x : ℂ)) := hbc.comp_left Complex.ofReal_zero
    have hi1 : Integrable (fun x => (b x : ℂ)) μ := hbC.integrable_of_hasCompactSupport hbcC
    have hi2 : Integrable (fun x => (b x : ℂ) * (h x - 1)) μ :=
      (hbC.mul (hh.sub continuous_const)).integrable_of_hasCompactSupport (hbcC.mul_right)
    have hi3 : Integrable (fun x => b x * (1 / 2 : ℝ)) μ :=
      (hbcont.integrable_of_hasCompactSupport hbc).mul_const _
    have split : (∫ x, (b x : ℂ) * h x ∂μ) = (∫ x, (b x : ℂ) ∂μ) + ∫ x, (b x : ℂ) * (h x - 1) ∂μ := by
      rw [← integral_add hi1 hi2]
      congr 1
      funext x
      ring
    have hbound : ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ ≤ ∫ x, b x * (1 / 2 : ℝ) ∂μ := by
      refine norm_integral_le_of_norm_le hi3 (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hbnn x)]
      by_cases hbx : b x = 0
      · rw [hbx]; simp
      · have hx : x ∈ Metric.ball (0 : E) (min δ δ') := hbs (subset_tsupport _ hbx)
        exact mul_le_mul_of_nonneg_left (hs x hx).le (hbnn x)
    have hreal : (∫ x, (b x : ℂ) ∂μ) = ((∫ x, b x ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [integral_mul_const] at hbound
    intro h0
    rw [split, hreal] at h0
    have e1 : ((∫ x, b x ∂μ : ℝ) : ℂ) = -∫ x, (b x : ℂ) * (h x - 1) ∂μ := eq_neg_of_add_eq_zero_left h0
    have e2 : ‖((∫ x, b x ∂μ : ℝ) : ℂ)‖ = ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ := by rw [e1, norm_neg]
    rw [Complex.norm_real, Real.norm_of_nonneg hbint.le] at e2
    linarith
  refine ⟨b, hbd, hbc, aux f hf fun x hx => ?_, aux g hg fun x hx => ?_⟩
  · have := hδf (lt_of_lt_of_le hx (min_le_left _ _))
    rwa [hf0, dist_eq_norm] at this
  · have := hδg (lt_of_lt_of_le hx (min_le_right _ _))
    rwa [hg0, dist_eq_norm] at this

local instance bsS {p : ℕ} : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
local instance bsRC {k p ρ : ℕ} : BorelSpace (U.RC k p ρ) := Prod.borelSpace

theorem piHaar {n p : ℕ} : (volume : Measure (Fin n → Fin p → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ => volume)

theorem rcHaar {k p ρ : ℕ} : (volume : Measure (U.RC k p ρ)).IsAddHaarMeasure := by
  have := @piHaar (2 * ρ + k + 1) p
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

theorem bump_exists {k p ρ : ℕ} (z z' : Fin (2 * ρ + k + 1) → ℂ) (hz : inWb k ρ z) (hz' : inWb k ρ z') :
    ∃ b : U.RC k p ρ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)) ≠ 0 ∧
      (∫ x, (b x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)) ≠ 0 := by
  have hc : Continuous (fun x : U.RC k p ρ => psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x)) :=
    (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)
  have hc' : Continuous (fun x : U.RC k p ρ => star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x))) :=
    ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)).star
  have h0 : psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ 0) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero]
    exact Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz) _
  have h0' : star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ 0)) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz') _, star_one]
  have := @rcHaar k p ρ
  unfold U.muRC
  exact bump_two volume _ _ hc hc' h0 h0'

end Formalism.FourierDecayAlt.P.CutEX.MkTopBump
end
end

