module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.PinModel

variable {D : D7} {u : D.what₂.Word}

theorem exists_finM (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a ∈ GfC V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, ha, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ha, ?_⟩
  have e2 : (finE V a : GL _ _) = y.1 := congrArg Subtype.val e
  rw [← e2]
  rfl

theorem exists_transport_adelic_correction {X : HidaSetting D} {F : Formalism.L2.Forms.Forms0 D u} (tr : Formalism.L2.SG.ColDict.Transport X u F) :
    ∃ a, IsTransportAdelicCorrection tr a := by
  obtain ⟨a, ha, e⟩ := exists_finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) tr.h0
  exact ⟨a, ha, e⟩

theorem exists_isTypePlaces : ∃ Pg : Finset (Pl D.host.E), GlobalTheory.Core.Mi.IsTypePlaces Pg := by
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ PP : Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := fun v => by
    have := v.isMaximal
    obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    refine ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, ?_⟩
    exact HeightOneSpectrum.ext hQ'.over.symm
  choose s hs using key
  have hne : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hfin : {v : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)})
      (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hne)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  refine ⟨hfin.toFinset.image s, ?_, ?_⟩
  · intro PP hPP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP
    have hv' : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := hfin.mem_toFinset.1 hv
    rw [← hs v] at hv'
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (s v).asIdeal := hv'
    rwa [map_natCast] at h2
  · intro v hv
    refine ⟨s v, ⟨Finset.mem_image.2 ⟨v, hfin.mem_toFinset.2 hv, rfl⟩, hs v⟩, ?_⟩
    rintro PP ⟨hPP, e⟩
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hPP
    rw [hs w] at e
    rw [e]

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)

end GlobalTheory.Core.Mi.PinModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

variable {D : D7}

def IsSkew (μ : D.host.E) : Prop := μ ≠ 0 ∧ star μ = -μ

def Tm (A : HSp D) (μ : D.host.E) : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) D.host.E :=
  (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e')).submatrix id finSumFinEquiv.symm

def IsChart (A : HSp D) (μ : D.host.E) (κ : GA D (dblSp A) ≃* G D A.rank) : Prop :=
  ∀ g, (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) * mat (κ g) = mt (dblSp A) g * rat (Tm A μ)

def IntA (z : AE D) : Prop := ∀ v, compFin D.host.F D.host.E v z ∈ intLoc D.host.F D.host.E v

def IntGL {n : ℕ} (M : GL (Fin n) (AE D)) : Prop := (∀ i j, IntA (M.1 i j)) ∧ ∀ i j, IntA ((M⁻¹).1 i j)

def ScalData (μ : D.host.E) (u ε : (AE D)ˣ) : Prop :=
  (ε : AE D) * u * cA D u = incA D μ ∧ IntA (ε : AE D) ∧ IntA ((ε⁻¹ : (AE D)ˣ) : AE D) ∧
    ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4

def HalfData (t : AE D) : Prop := t + cA D t = 1 ∧ IntA t ∧ ∀ w, compInf D.host.F D.host.E w (2 * t) = 1

def IsConj (A : HSp D) (a : GL (Fin A.rank) (AE D)) (κ : GA D (dblSp A) ≃* G D A.rank) (p : siegel A) : Prop :=
  ∀ k : GA D (dblSp A), k ∈ Khat A a ↔ κ ((p : GA D (dblSp A))⁻¹ * k * p) ∈ K D A.rank

def hgtStd (A : HSp D) (a : GL (Fin A.rank) (AE D)) (κ : GA D (dblSp A) ≃* G D A.rank) (p : siegel A) :
    G D A.rank → ℝ≥0 := fun g => hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹) * absA D (aP A p)

def IsTransport (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B))
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (κ : GA D (dblSp A) ≃* G D A.rank)
    (ω : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)) : Prop :=
  ∀ g f, IsThetaFunO ψ (dblSp A) B f → ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 f →
    (ω (κ g) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f)

def shift (ψ : AddChar (AF D.host.F) ℂ) (l : D.host.F) : AddChar (AF D.host.F) ℂ :=
  ψ.mulShift (algebraMap D.host.F (AF D.host.F) l)

def stdInv (n : ℕ) (μ : D.host.E) (τ : D.what₂.Tau) : Matrix (Fin (n + n)) (Fin (n + n)) ℂ :=
  (tauE D τ μ / (‖tauE D τ μ‖ : ℂ)) • blk4 0 1 (-1) 0

def IsStdInv (A : HSp D) (μ : D.host.E)
    (s : D.what₂.Tau → Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) ℂ) : Prop :=
  ∀ τ, s τ * (Tm A μ).map (tauE D τ) = (Tm A μ).map (tauE D τ) * stdInv A.rank μ τ

variable (V : HSp D) {n : ℕ} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)

def linF (τ : D.what₂.Tau) (X z : Matrix (Fin V.rank) (Fin n) ℂ) : ℂ :=
  ((4 * Real.pi * |l τ| * (Matrix.trace (Xᴴ * (gramAt D V τ * s τ) * z)).re : ℝ) : ℂ)

def annS (θ : InfFam D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) (φ : Mx D V.rank n → ℂ) :
    Mx D V.rank n → ℂ :=
  fun x => deriv (fun t : ℝ => φ (x + lineAt θ τ X t)) 0 + linF V l s τ X (compAt θ τ x) * φ x


open Classical in
def annC (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin n) ℂ) (f : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ) :
    (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ :=
  fun z => deriv (fun t : ℝ => f (z + t • (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ))) 0 + linF V l s τ X (Matrix.of (z τ)) * f z

end GlobalTheory.StdUnn

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def IsBiSmooth {A S A' : HSp D} (C : WO A S → WO S A' → ℂ) : Prop :=
  ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO A S) (L' : (Fin n → ℝ) →+ WO S A'), Continuous L → Continuous L' →
    (∀ t, (L t).map (finPart D) = 0) → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ u v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => C (u + L t) (v + L' t)

structure IsBiTheta (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (C : WO A S → WO S A' → ℂ) : Prop where
  cont : Continuous fun p : WO A S × WO S A' => C p.1 p.2
  smooth : IsBiSmooth C
  quasiL : ∀ γ u v, C (ratW S A γ + u) v = ψ (-(symplOH A S (ratW S A γ) u)) * C u v
  quasiR : ∀ γ u v, C u (ratW A' S γ + v) = ψ (-(symplOH S A' (ratW A' S γ) v)) * C u v
  levL : ∃ U : AddSubgroup (WO A S), IsOpen (U : Set (WO A S)) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ v, heisO ψ A S a (fun u => C u v) = fun u => C u v
  levR : ∃ U : AddSubgroup (WO S A'), IsOpen (U : Set (WO S A')) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ u, heisO ψ S A' a (C u) = C u

def BiAct (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'),
    IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C →
      (∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u) ∧
      (∀ q, IsBiTheta ψ A S A' fun u v => omb q (C u) v) ∧
      (∀ p q u v, omb q (fun v' => oma p (fun u' => C u' v') u) v = oma p (fun u' => omb q (C u') v) u) ∧
      Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
        omb x.2.1 (fun v => oma x.1 (fun u => C u v) x.2.2.1) x.2.2.2

def FockRed (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'),
    x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
    ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C →
      ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank),
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ)

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

end Dat

section Examples

variable {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D}

end Examples

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSphGL
section
noncomputable section

namespace GlobalTheory.Core.Rk.SWQ

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart)

section Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m n N : ℕ}

def IntM {ι κ : Type} (x : Matrix ι κ (w.adicCompletion E)) : Prop := ∀ i j, x i j ∈ Ov E w

def mob (q r : ℕ) : ℂ := (-1) ^ r * (q : ℂ) ^ (r * (r - 1) / 2)

def cOne (q : ℕ) (z : ℂˣ) (σ : ℂ) (r : ℕ) : ℂ := mob q r * (z : ℂ) ^ r * (q : ℂ) ^ (-(σ * r))



end Local

section Adelic

variable {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

def cw (h : w.under (𝓞 D.host.F) = q) : AE D →+* w.adicCompletion D.host.E := (toCompl h).comp (compFin D.host.F D.host.E q)

def offM (q : FinPl D) {m n : ℕ} (x : Mx D m n) : Mx D m n :=
  x - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) • x

end Adelic

end GlobalTheory.Core.Rk.SWQ

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStageTrivialTwist
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainTw.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



theorem one_lt_norm (PP : Pl D.host.E) : (1 : ℝ) < (Ideal.absNorm PP.asIdeal : ℝ) := by
  exact_mod_cast GlobalTheory.LFun.one_lt_absNorm PP

theorem zinv_pos (PP : Pl D.host.E) (a b : ℕ) : 0 < zinv PP a b := by
  refine Finset.prod_pos fun n hn => sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ (one_lt_norm PP) ?_))
  have := (Finset.mem_Ioc.1 hn).1
  omega

theorem zinv_mul (PP : Pl D.host.E) {a b c : ℕ} (h : a ≤ b) (h' : b ≤ c) : zinv PP a b * zinv PP b c = zinv PP a c :=
  Finset.prod_Ioc_consecutive _ h h'

theorem idx_vol (PP : Pl D.host.E) (k : ℕ) :
    idxQ PP (k + 1) * volOne PP (k + 1) * zinv PP D.R.t ((k + 1) * D.R.t) = zinv PP D.R.t (D.R.r + (k + 1) * D.R.t) := by
  have h1 : D.R.t ≤ (k + 1) * D.R.t := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  have e1 := zinv_mul PP (Nat.zero_le D.R.t) h1
  have e2 := zinv_mul PP (Nat.zero_le D.R.t) (h1.trans (Nat.le_add_left _ D.R.r))
  have p0 := (zinv_pos PP 0 D.R.t).ne'
  have p1 := (zinv_pos PP 0 D.R.r).ne'
  have p2 := (zinv_pos PP D.R.t ((k + 1) * D.R.t)).ne'
  have p3 : (Ideal.absNorm PP.asIdeal : ℝ) ≠ 0 := (zero_lt_one.trans (one_lt_norm PP)).ne'
  unfold idxQ volOne
  rw [← e1, ← e2]
  field_simp

theorem const_eq {c : Com D} {s s' : PiLocalization₂ D} (w : Twist D) (k : ℕ) (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V))
    (mR : Measure (GinfC s.V)) (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec) (L H H₀ : ℂ)
    (hH : H₀ = H * ∏ PP ∈ w.Q, blockL c k PP) (h0 : dS w.S₀ s s' ≠ 0)
    (hd : dS (c.S : Set _) s s' = dS w.S₀ s s' * ((∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t) : ℝ) : ℂ)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℂ) * (L * H / dS (c.S : Set _) s s') * locQ c w k * ∫ g, zReal p m X φ v g ∂mR =
      kapOf w k p m X mR φ v H₀ * L := by
  have e : (∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t)) =
      (∏ PP ∈ w.Q, idxQ PP (k + 1)) * (∏ PP ∈ w.Q, volOne PP (k + 1)) * ∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun PP _ => (idx_vol PP k).symm
  have n : (∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t)) ≠ 0 :=
    (Finset.prod_pos fun PP _ => zinv_pos PP _ _).ne'
  rw [e] at n
  have n1 : ((∏ PP ∈ w.Q, idxQ PP (k + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul (left_ne_zero_of_mul n)
  have n2 : ((∏ PP ∈ w.Q, volOne PP (k + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul (left_ne_zero_of_mul n)
  have n3 : ((∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul n
  have l : locQ c w k = (∏ PP ∈ w.Q, blockL c k PP) * ((∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) : ℝ) : ℂ) := by
    rw [locQ, Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [kapOf, hd, e, l, hH, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_div]
  field_simp

end GlobalTheory.ChainTw.Check

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainTw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def trivAt (Pg P : Finset (Pl D.host.E)) (r : ℕ) : Subgroup (G0 P r) where
  carrier := {g | ∀ PP : P, PP.1 ∈ Pg → g PP = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb PP h => by rw [Pi.mul_apply, ha PP h, hb PP h, mul_one]
  inv_mem' := fun {a} ha PP h => by rw [Pi.inv_apply, ha PP h, inv_one]


open Classical in
def comR (t : T) : Com D :=
  ⟨R.θ, R.ψ, R.toLevCh.mu t, R.eta, R.Pg ∪ R.Q t, ⟨trivAt R.Pg (R.Pg ∪ R.Q t) D.R.r, 1⟩,
    fun j PP => if PP ∈ R.Q t then (R.xiR t PP)⁻¹ else R.chi j PP⟩

def twR (t : T) : Twist D := ⟨R.Pg, R.Q t, R.chi, R.xiR t⟩

def stY (t : T) (j : ℕ) : PiLocalization₂ D :=
  ⟨Yc D j, parB (Ptw D) (min j D.R.m), R.MY j, R.ΛY j, R.βY j, R.datYt t j R.triv, R.νY t j, R.fdY t j⟩

def stX (t : T) : PiLocalization₂ D := ⟨D.sp.X', parB (Ptw D) D.R.m, R.MX, R.ΛX, R.βX, R.datXt t, R.νX t, R.fdX t⟩

def RangeX : Prop := ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
  MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (Lev.levChi _ R.βX (R.datXt t))

def stepY (t : T) (k : ℕ) : Step (comR R t) (stY R t k) (stY R t (k + 1)) := ⟨R.ωY t k, R.vY t k, R.ItY k, R.ioY t k⟩

def stepX (h : RangeX R) (t : T) : Step (comR R t) (stY R t (D.R.m - 1)) (stX R t) :=
  ⟨R.ωX t, R.vX t, R.ItX, (R.ioX t ∘ₗ (LinearEquiv.ofEq _ _ (h t).symm).toLinearMap :
    MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (Lev.levChi _ R.βX (R.datXt t)) →ₗ[ℂ] R.CC t (D.R.m - 1))⟩

def toCC (h : RangeX R) (t : T) (x : (R.HX t).H) : (stX R t).CC (comR R t) :=
  LinearEquiv.ofEq _ _ (h t) ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict x)

def RChain (h : RangeX R) : Prop := ∀ t, (twR R t).Is (comR R t) ∧ (∀ j < D.R.m, IsStage (comR R t) (twR R t) j (stY R t j)) ∧
  IsStage (comR R t) (twR R t) D.R.m (stX R t) ∧ (∀ k, k + 1 < D.R.m → IsStep (twR R t) (k + 1) (stepY R t k)) ∧
  IsStep (twR R t) D.R.m (stepX R h t)

def NormX (h : RangeX R) : Prop := ∃ δ : ℝ, 0 < δ ∧ ∀ t, Function.Bijective (toCC R h t) ∧
  ∀ ipD ip, IsMet (comR R t) (stX R t) ipD ip → ∀ x y : (R.HX t).H, ⟪x, y⟫_ℂ = (δ : ℂ) * ip (toCC R h t y) (toCC R h t x)

def RMeas : Prop := ∀ j < D.R.m, ∃ mR : Measure (GinfC (Yc D j)), ∀ t, IsLevMeas (stY R t j) mR

def RVol : Prop := ∀ t, (∀ j < D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D j) (R.νY t j) =
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D j) (R.νY A.μ0 j) * ∏ PP ∈ R.Q t, idxQ PP j ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D j) (R.νY t j)) ∧
  GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX t) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX A.μ0) * ∏ PP ∈ R.Q t, idxQ PP D.R.m ∧
  0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX t)

def RNrm : Prop := ∀ t, (∀ k, k + 1 < D.R.m → ∀ m X, IsCovolOne (ratL (Yc D (k + 1)) (Yc D k)) m X →
    nrm2 m X (R.vY t k) = nrm2 m X (R.vY A.μ0 k) * ∏ PP ∈ R.Q t, volOne PP (k + 1)) ∧
  ∀ m X, IsCovolOne (ratL D.sp.X' (Yc D (D.R.m - 1))) m X → nrm2 m X (R.vX t) = nrm2 m X (R.vX A.μ0) * ∏ PP ∈ R.Q t, volOne PP D.R.m

def IsUnif (k : ℕ) (s s' : T → PiLocalization₂ D) (p : ∀ t, Step (comR R t) (s t) (s' t)) (K : ℂ)
    (P : ∀ t, PolF D (s' t).V.rank (s t).V.rank) (v : ∀ t, (s t).M.Vec) : Prop :=
  K ≠ 0 ∧ ∀ t, ∃ m X mR H₀, IsCovolOne (ratL (s' t).V (s t).V) m X ∧ IsLevMeas (s t) mR ∧
    RealConv (p t) m X (P t) (v t) mR ∧ IsHval (comR R t) (twR R t).S₀ k H₀ ∧ kapOf (twR R t) k (p t) m X mR (P t) (v t) H₀ = K

def RUnif (h : RangeX R) : Prop :=
  (∀ k, k + 1 < D.R.m → ∃ (K : ℂ) (φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank) (v : (R.MY k).Vec),
    IsUnif R k (fun t => stY R t k) (fun t => stY R t (k + 1)) (fun t => stepY R t k) K (fun _ => φ) fun _ => v) ∧
  ∃ (K : ℂ) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec),
    IsUnif R (D.R.m - 1) (fun t => stY R t (D.R.m - 1)) (fun t => stX R t) (fun t => stepX R h t) K (fun _ => φ) fun _ => v

def RowPar : Prop := ∀ (t : T) (c : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.EigSys D),
  (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c ≠ ⊥ → ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B) ∧
  ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c, ∃ hu : PiTensorProduct.lift u ∈ (stY R t 0).CC (comR R t),
    u ≠ 0 → ∀ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B →
      IsPar (c := comR R t) (s := stY R t 0) ⟨_, hu⟩ B

def IPDict : Prop := ∀ t, ∀ k < D.R.m, ∀ ipD ip, IsMet (comR R t) (stY R t k) ipD ip → ∀ (x y : (stY R t k).CC (comR R t)) (a : ℂ),
  GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t k (PiTensorProduct.lift.symm x.1) (PiTensorProduct.lift.symm y.1) a ↔ a = ip y x

def StepExactNS (D : D7) : Prop := ForStepQ D fun c w k s s' p => ∀ ipD ip, IsMet c s ipD ip → ∀ m X, IsCovolOne (ratL s'.V s.V) m X →
  ∀ mR, IsLevMeas s mR → ∀ φ v, RealConv p m X φ v mR → ∀ (u₁ u₂ : s.CC c) B, IsPar u₁ B → IsQ w k u₁ →
    (∃ q ∉ c.S, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q ∧ GlobalTheory.Core.Rk.SW.NSAt B (c.chT (k + 1)) D.R.t q) →
    ∀ l, GlobalTheory.Cont.HolValueAt (fun z => GlobalTheory.LFun.LSD D c.S B (c.chT (k + 1)) (z + 1 / 2)) ((D.R.t : ℂ) / 2) l →
      s'.pet (p.up φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v))) (p.up φ (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v))) =
        conj ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℂ) * (l / dS (c.S : Set _) s s') * locQ c w k * ∫ g, zReal p m X φ v g ∂mR) * ip u₁ u₂

end GlobalTheory.ChainTw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.UpNeNSOfUpNe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainNS

open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def invFam (B : GlobalTheory.LFun.Fam D.host.E) : GlobalTheory.LFun.Fam D.host.E := fun w => (B w).map (·⁻¹)

def ParBoundInv (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (invFam B) s.V.rank ((s.V.rank : ℝ) / 2)

def ChainNS (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ S' : Finset (HeightOneSpectrum (𝓞 D.host.F)), c.S ⊆ S' →
  ∀ B : GlobalTheory.LFun.Fam D.host.E,
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) →
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))) (invFam B) D.R.r ((D.R.r : ℝ) / 2) →
    ∀ k < D.R.m, ∃ q ∉ S', Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q ∧
      GlobalTheory.Core.Rk.SW.NSAt (chainPar c B k) (c.chT (k + 1)) D.R.t q

end GlobalTheory.ChainNS

end
end

