module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem mul_mem_UAt {n : ℕ} {Y : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {g h : UA σ Y.J}
    (hg : g ∈ UAt σ Y ev) (hh : h ∈ UAt σ Y ev) : g * h ∈ UAt σ Y ev := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    simp only [mat, Subgroup.coe_mul, Units.val_mul]; noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem mat_mul {n : ℕ} {Y : Spc F E n} (g h : UA σ Y.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {n : ℕ} {Y : Spc F E n} : mat (1 : UA σ Y.J) = 1 := rfl

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem pres (hT : IsTriple B G X om om') (p : UA σ G.V.J × UA σ G.W.J) {Φ : (Fin a × Fin (a + a') → AF F) → ℂ}
    (hΦ : Φ ∈ schA F (Fin a × Fin (a + a'))) : om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
  (IsUWeilPair.isUSplitting hT.weil).pres p Φ hΦ

theorem acts_comp (hT : IsTriple B G X om om') {v : Pl (F := F)} {h₁ h₂ : UA σ G.W.J}
    {φ φ₂ φ₃ : (Fin a × Fin (a + a') → Fv F v) → ℂ}
    (h2 : Acts (evFin F v) (om (1, h₂)) φ φ₂) (h1 : Acts (evFin F v) (om (1, h₁)) φ₂ φ₃) :
    Acts (evFin F v) (om (1, h₁ * h₂)) φ φ₃ := by
  intro r hr
  have hr2 : Rest (evFin F v) φ₂ r := ⟨hr.1, by rw [← h2 r hr]; exact pres hT _ hr.2⟩
  have e : om (1, h₁ * h₂) = om (1, h₁) * om (1, h₂) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply, h2 r hr, h1 r hr2]

theorem acts_one {v : Pl (F := F)} (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) :
    Acts (evFin F v) (om (1, 1)) φ φ := by
  intro r _
  rw [show ((1, 1) : UA σ G.V.J × UA σ G.W.J) = 1 from rfl, map_one, Module.End.one_apply]

noncomputable section

def cmpGL {n : ℕ} {Y : Spc F E n} {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) : GL (Fin n) (Fv F v) :=
  Units.map (piW t).mapMatrix.toMonoidHom h.1

theorem cmpGL_val {n : ℕ} {Y : Spc F E n} {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) :
    (cmpGL t h).1 = (mat h).map (piW t) := rfl

def apowHom {v : Pl (F := F)} (z : ℂ) : (Fv F v)ˣ →* ℂˣ where
  toFun x := Units.mk0 (GlobalTheory.SplitFlip.apow x z) (GlobalTheory.SplitFlip.apow_ne_zero x z)
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by simp [GlobalTheory.SplitFlip.apow_mul])

end

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isUnit_det_cmp {n : ℕ} {Y : Spc F E n} {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (h : UA σ Y.J) :
    IsUnit ((mat h).map (piW t)).det := by
  rw [← cmpGL_val]; exact (Matrix.isUnit_iff_isUnit_det _).1 (cmpGL t h).isUnit

theorem two_ne_zero_Fv (v : Pl (F := F)) : (2 : Fv F v) ≠ 0 := by
  have := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
  rwa [map_ofNat, map_zero] at this

theorem core (hT : IsTriple B G X om om') (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ))
    (hEx : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃! φ₁, φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om (1, h)) φ φ₁)
    (hsurj : ∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1)
    (hinj : ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂)
    (hS : ∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) :
    ∃ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) := by
  classical
  by_cases h0 : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ = 0
  · refine ⟨1, fun h _ => ⟨cmpGL t h, rfl, fun φ hφ φ₁ hφ₁ _ => ?_⟩⟩
    rw [h0 φ₁ hφ₁, h0 φ hφ]
    funext Y
    simp [GlobalTheory.SplitFlip.omA]
  push Not at h0
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.1 hne
  set P : UA σ G.W.J → ℂ → Prop := fun h c => ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ) with hP
  have uniq : ∀ h ∈ UAt σ G.W (evFin F v), ∀ c c', P h c → P h c' → c = c' := by
    intro h hh c c' hc hc'
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hEx h hh φ₀ hφ₀
    set M := (mat h).map (piW t)
    have key : Y₀ * Mᵀ * M⁻¹ᵀ = Y₀ := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (isUnit_det_cmp t h),
        Matrix.transpose_one, Matrix.mul_one]
    have e1 := hc φ₀ hφ₀ φ₁ hφ₁ hA (Y₀ * Mᵀ)
    have e2 := hc' φ₀ hφ₀ φ₁ hφ₁ hA (Y₀ * Mᵀ)
    rw [key] at e1 e2
    exact mul_right_cancel₀ hY₀ (e1.symm.trans e2)
  let c : UA σ G.W.J → ℂ := fun h => if hh : h ∈ UAt σ G.W (evFin F v) then (hS h hh).choose else 0
  have hc : ∀ h (hh : h ∈ UAt σ G.W (evFin F v)), P h (c h) := by
    intro h hh
    simp only [c, dif_pos hh]
    exact (hS h hh).choose_spec
  have P1 : P 1 1 := by
    intro φ hφ φ₁ hφ₁ hA Y
    have : φ₁ = φ := (hEx 1 (one_mem_UAt _ _) φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ, acts_one φ⟩
    subst this
    rw [mat_one, Matrix.map_one (piW t) (map_zero _) (map_one _), inv_one, Matrix.transpose_one, Matrix.mul_one,
      one_mul]
  have c1 : c 1 = 1 := uniq 1 (one_mem_UAt _ _) _ _ (hc 1 (one_mem_UAt _ _)) P1
  have Pmul : ∀ h₁ (hh₁ : h₁ ∈ UAt σ G.W (evFin F v)) h₂ (hh₂ : h₂ ∈ UAt σ G.W (evFin F v)),
      P (h₁ * h₂) (c h₁ * c h₂) := by
    intro h₁ hh₁ h₂ hh₂ φ hφ φ₁₂ hφ₁₂ hA Y
    obtain ⟨φ₂, ⟨hφ₂, hA2⟩, -⟩ := hEx h₂ hh₂ φ hφ
    obtain ⟨φ₃, ⟨hφ₃, hA3⟩, -⟩ := hEx h₁ hh₁ φ₂ hφ₂
    have : φ₁₂ = φ₃ := (hEx (h₁ * h₂) (mul_mem_UAt hh₁ hh₂) φ hφ).unique ⟨hφ₁₂, hA⟩ ⟨hφ₃, acts_comp hT hA2 hA3⟩
    subst this
    rw [hc h₁ hh₁ φ₂ hφ₂ φ₁₂ hφ₁₂ hA3, hc h₂ hh₂ φ hφ φ₂ hφ₂ hA2, mat_mul, Matrix.map_mul, Matrix.mul_inv_rev,
      Matrix.transpose_mul, Matrix.mul_assoc, mul_assoc]
  have cmul : ∀ h₁ (hh₁ : h₁ ∈ UAt σ G.W (evFin F v)) h₂ (hh₂ : h₂ ∈ UAt σ G.W (evFin F v)),
      c (h₁ * h₂) = c h₁ * c h₂ := fun h₁ hh₁ h₂ hh₂ =>
    uniq _ (mul_mem_UAt hh₁ hh₂) _ _ (hc _ (mul_mem_UAt hh₁ hh₂)) (Pmul h₁ hh₁ h₂ hh₂)
  choose sec hsec hsecv using hsurj
  have secmul : ∀ g₁ g₂, sec (g₁ * g₂) = sec g₁ * sec g₂ := fun g₁ g₂ =>
    hinj _ (hsec _) _ (mul_mem_UAt (hsec g₁) (hsec g₂)) (by
      rw [hsecv, mat_mul, Matrix.map_mul, hsecv, hsecv, Units.val_mul])
  have sec1 : sec 1 = 1 := hinj _ (hsec _) _ (one_mem_UAt _ _) (by
      rw [hsecv, mat_one, Matrix.map_one (piW t) (map_zero _) (map_one _), Units.val_one])
  let κ : GL (Fin (a + a')) (Fv F v) →* ℂ :=
    { toFun := fun g => c (sec g)
      map_one' := by simp only [sec1, c1]
      map_mul' := fun g₁ g₂ => by simp only [secmul, cmul _ (hsec g₁) _ (hsec g₂)] }
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (two_ne_zero_Fv v) κ.toHomUnits
  refine ⟨χ * apowHom ((a : ℂ) / 2), fun h hh => ⟨cmpGL t h, rfl, fun φ hφ φ₁ hφ₁ hA => ?_⟩⟩
  have hsh : sec (cmpGL t h) = h := hinj _ (hsec _) _ hh (by rw [hsecv, cmpGL_val])
  have hch : c h = (χ (Matrix.GeneralLinearGroup.det (cmpGL t h)) : ℂ) := by
    have := congrArg Units.val (hχ (cmpGL t h))
    rw [MonoidHom.coe_toHomUnits] at this
    rw [← this]
    show c h = c (sec (cmpGL t h))
    rw [hsh]
  funext Y
  rw [hc h hh φ hφ φ₁ hφ₁ hA Y, hch]
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitFlip.invT_val, map_one, inv_one, Units.val_one, MonoidHom.mul_apply,
    Units.val_mul, Fintype.card_fin, GlobalTheory.SplitFlip.apow_one, one_mul, Matrix.one_mul, Matrix.coe_units_inv, cmpGL_val]
  have hv : ((apowHom (v := v) ((a : ℂ) / 2) (GlobalTheory.SplitFlip.gdet (cmpGL t h)) : ℂˣ) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (cmpGL t h)) (-(a : ℂ) / 2) = 1 := by
    show GlobalTheory.SplitFlip.apow _ _ * GlobalTheory.SplitFlip.apow _ _ = 1
    rw [← GlobalTheory.SplitFlip.apow_add, show (a : ℂ) / 2 + -(a : ℂ) / 2 = 0 by ring, GlobalTheory.SplitFlip.apow_zero]
  rw [mul_one, mul_assoc (χ _ : ℂ), hv, mul_one]

end GlobalTheory.LocalUnitSubgroupClosure

namespace GlobalTheory.LocalUnitSubgroupClosure

theorem linear_weil_functional_character_weight_zero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) →
    ∃ β₀ : (Fv F v)ˣ →* ℂˣ, (∀ h ∈ UAt σ G.W (evFin F v), ∃ h' : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA 1 β₀ 1 h' (ι φ)) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι _ hS
  have hEx := (GlobalTheory.T.theta_action_exists hPr F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1 1 (one_mem_UAt _ _)
  exact core hT v t ι hEx (_root_.GlobalTheory.SkewLevi.surj_at_place hPr F E σ B a a' G X om om' hT v hv t)
    (_root_.GlobalTheory.UnitaryInjAtPlace.eq_of_piW_eq F E σ B a a' G X om om' hT v hv t) hS

end GlobalTheory.LocalUnitSubgroupClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDepthStableUnderPrimePowPerturbation
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PertDepth

theorem nval_neg_eq (T : CDVR) (e : ℕ) (x : T.Fr) : nval T.V e (-x) = nval T.V e x := by
  by_cases hx : x = 0
  · subst hx; rw [neg_zero]
  · rw [nval_of_ne (neg_ne_zero.2 hx), nval_of_ne hx]
    simp only [vV, Valuation.map_neg]

theorem iInf_nval_add_eq (T : CDVR) (e : ℕ) {ι : Type*} (Q : ι → Prop) (A D : ι → T.Fr) (M : EReal)
    (hD : ∀ i, Q i → M ≤ nval T.V e (D i)) (hA : ⨅ (i) (_ : Q i), nval T.V e (A i) < M) :
    ⨅ (i) (_ : Q i), nval T.V e (A i + D i) = ⨅ (i) (_ : Q i), nval T.V e (A i) := by
  set Y := ⨅ (i) (_ : Q i), nval T.V e (A i) with hY
  set X := ⨅ (i) (_ : Q i), nval T.V e (A i + D i) with hX
  have hge : min Y M ≤ X := le_iInf₂ fun i hi =>
    le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) (nval_add e (A i) (D i))
  have hle : min X M ≤ Y := le_iInf₂ fun i hi => by
    have h1 := nval_add (V := T.V) e (A i + D i) (-D i)
    rw [add_neg_cancel_right, nval_neg_eq] at h1
    exact le_trans (min_le_min (iInf₂_le i hi) (hD i hi)) h1
  have h1 : Y ≤ X := by rwa [min_eq_left hA.le] at hge
  have h2 : X ≤ Y := by
    rcases le_total X M with h | h
    · rwa [min_eq_left h] at hle
    · rw [min_eq_right h] at hle; exact absurd (lt_of_le_of_lt hle hA) (lt_irrefl _)
  exact le_antisymm h2 h1

theorem nval_pow_p (T : CDVR) (p e : ℕ) (he : 0 < e) (hp : vV T.V (p : T.Fr) = e) (N : ℕ) :
    nval T.V e ((p : T.Fr) ^ N) = ((N : ℝ) : EReal) := by
  have hp0 : (p : T.Fr) ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp [vV] at hp
    omega
  have h1 : nval T.V e (p : T.Fr) = ((1 : ℝ) : EReal) := by
    rw [nval_of_ne hp0, hp]
    congr 1
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    push_cast
    field_simp
  induction N with
  | zero =>
    rw [pow_zero, nval_of_ne one_ne_zero]
    simp [vV]
  | succ N ih =>
    rw [pow_succ, nval_mul, ih, h1, ← EReal.coe_add]
    push_cast
    rfl

end GlobalTheory.PertDepth


open GlobalTheory.PertDepth in
theorem GlobalTheory.nuLocOf_pert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → vV T.V (p : T.Fr) = e → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N k : ℕ) (ρ B : ℝ) (P₀ R : MvPolynomial (LtN Dw n) T.Fr), ChBound Ch e ρ a n → R ∈ FFV (Dw := Dw) T a n → nuLocOf Ch e k P₀ ≤ (B : EReal) → B + ρ < N → nuLocOf Ch e k (P₀ + ((p : T.Fr) ^ N) • R) = nuLocOf Ch e k P₀ := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p T io y Ch e he hp a n N k ρ B P₀ R hCh hR hP₀ hBN
  letI := io.toAlgebra
  have hRv : ∀ f : PS T.Fr n Ch.ch.d, IsIntPS T f →
      ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f (fun ℓ => ℓ.2.2)
        (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) R) := by
    intro f hf
    have h1 := hCh k
    rw [nuLocC_eq_iInf] at h1
    exact le_trans h1 (le_trans (iInf₂_le R hR) (iInf₂_le f hf))
  unfold nuLocOf
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_addP, Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf.nabValN_smulP]
  refine iInf_nval_add_eq T e _ _ _ (((N : ℝ) - ρ : ℝ) : EReal) (fun f hf => ?_) ?_
  · rw [nval_mul, nval_pow_p T p e he hp N]
    have := add_le_add (le_refl ((N : ℝ) : EReal)) (hRv f hf)
    rw [← EReal.coe_add] at this
    simpa [sub_eq_add_neg] using this
  · refine lt_of_le_of_lt hP₀ ?_
    exact EReal.coe_lt_coe_iff.2 (by linarith)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjective
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LagrCoord

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  intro h0
  apply hD
  rw [← hA, ← Matrix.det_submatrix_equiv_self e.symm,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) e.symm Function.bijective_id,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) id Function.bijective_id,
    Matrix.det_mul, Matrix.det_mul, Matrix.submatrix_id_id, h0, mul_zero, zero_mul]

theorem det_ne_zero_of_hasSig_smul {n r s : ℕ} {c : ℂ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig (c • M) r s) :
    M.det ≠ 0 := by
  intro h0
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, h0, mul_zero]

theorem det_ne_zero_of_map {E : Type} [CommRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) x ∧ x.map (piW t) = 0 ∧ -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = Y := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Y
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hXd : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig (hX.sig w))
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_map W.J (B.emb w).1 (det_ne_zero_of_hasSig_smul (hW.sig w))
  have ht : Function.Injective t := t.toRingHom.injective
  have hXt : IsUnit (X.J.map t).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hXd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom X.J)
  have hWt : IsUnit ((W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    apply hWd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom W.J)
  obtain ⟨x, hxat, hx0, hx1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hB.cm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
    (-((X.J.map t)⁻¹ * Y * ((W.J.map t)ᵀ)⁻¹))
  refine ⟨x, hxat, hx0, ?_⟩
  rw [hx1]
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWt, Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hXt]

end GlobalTheory.LagrCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Div.CoordOpp

theorem piW_inclR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (e : E) :
    piW t (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = t e := by
  have h1 : compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Fv F v) e := by
    simp [compFin, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  simp only [piW, RingHom.comp_apply, h1]
  exact splitProj_inclR t e

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [piW, cA, compFin, splitProj]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem incM_map_piW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {m k : Type} (J : Matrix m k E) :
    (incM F J).map (piW t) = J.map t := by
  ext i j
  simp [incM, piW_inclR]

theorem unit_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) :
    ((mat g).map (piW t))ᵀ * J.map t * (mat g).map (piW (t.comp σ)) = J.map t := by
  have hg := g.2
  change ((mat g))ᵀ * incM F J * (mat g).map (cA σ) = incM F J at hg
  have := congrArg (fun M => M.map (piW t)) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, incM_map_piW] at this
  have e2 : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    ext i j; simp [piW_cA]
  rw [e2] at this
  simpa [Matrix.transpose_map] using this

end GlobalTheory.Div.CoordOpp

open GlobalTheory.Div.CoordOpp in
theorem GlobalTheory.Div.CoordOpp.coord_opp_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (g : UA σ X.J) (h : UA σ W.J)
    (x : Matrix (Fin n) (Fin d) (AE F E)),
    ((mat g).map (piW t))ᵀ * -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (mat g * x * (mat h)ᵀ).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) * (mat h).map (piW t) = -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) := by
  intro F E _ _ _ _ _ σ n d X W v t g h x
  have hg := unit_map σ g t
  have hh := unit_map σ h t
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.map_mul,
    Matrix.transpose_map, Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  set gt := (mat g).map (piW t)
  set gb := (mat g).map (piW (t.comp σ))
  set ht := (mat h).map (piW t)
  set hb := (mat h).map (piW (t.comp σ))
  set xb := x.map (piW (t.comp σ))
  have hh' : hbᵀ * (W.J.map t)ᵀ * ht = (W.J.map t)ᵀ := by
    have := congrArg Matrix.transpose hh
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  calc gtᵀ * (X.J.map t * (gb * xb * ((mat h)ᵀ).map (piW (t.comp σ))) * (W.J.map t)ᵀ) * ht
      = (gtᵀ * X.J.map t * gb) * xb * (hbᵀ * (W.J.map t)ᵀ * ht) := by
        simp only [hb, Matrix.transpose_map, Matrix.mul_assoc]
    _ = X.J.map t * xb * (W.J.map t)ᵀ := by rw [hg, hh']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHost
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.Period

theorem period_eq_kronecker : ∀ (D : D7) (L : SizeData₂ D) (Q : Par D), Q.PinHost → ∀ (Del h0 : ℕ), ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d), GlobalTheory.IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = (ofRecord D L Del h0).logOm ∧ (ofRecord D L Del h0).logOm = L.logOm ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField Q.H := by
  intro D L Q hp Del h0
  obtain ⟨i, χ, hχ, e⟩ := GlobalTheory.LamF.exists_kronecker_logOm_eq D Q hp L
  exact ⟨i, χ, hχ, e.trans (Formalism.L2.DIV.ofRecord_logOm D L Del h0).symm,
    Formalism.L2.DIV.ofRecord_logOm D L Del h0, GlobalTheory.FlatRow.isHostField D Q.H hp.1⟩

end GlobalTheory.CovTop.Period
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponent
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.BddCusp

theorem mul_mem_cuspOn_of_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : Rul Xo c), Nonempty (KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → Even G₀.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G₀.1 (τ, j) ≤ G₀.1 (τ, i)) → s ∈ secZ Xo c (exZ Dw G₀) → s ∈ suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C) → ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + G₀) := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s hK hU hpq h0 hdec hs hZ hb G hG f hf
  exact mul_mem_cuspOn_of_isSec h0 hs hZ
    (fun σ hσ k => _root_.GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU E H Dw l Xo c σ r (U σ) hK hσ (hU σ hσ) hpq G₀ h0 hdec s hs k) hb hG hf

end GlobalTheory.BddCusp
end

