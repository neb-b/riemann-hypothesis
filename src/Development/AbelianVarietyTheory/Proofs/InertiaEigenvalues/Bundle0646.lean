module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.MainFinal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinReciprocityMapUnique
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.ArtinUniq

variable {E : Type} [Field E] [NumberField E]

theorem eq_one_of_unit_unif {B : Type} [Group B] (v : HeightOneSpectrum (𝓞 E)) (f : (v.adicCompletion E)ˣ →* B)
    (hu : ∀ x, IsUnitAt v x → f x = 1) (hp : ∀ x, IsUnifAt v x → f x = 1) (x : (v.adicCompletion E)ˣ) : f x = 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E v
  have hv : Valued.v ((π : E) : v.adicCompletion E) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hπ0 : ((π : E) : v.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  let p : (v.adicCompletion E)ˣ := Units.mk0 _ hπ0
  have hpv : Valued.v (p : v.adicCompletion E) = WithZero.exp (-1) := hv
  have hfp : f p = 1 := hp p hpv
  have key : ∀ n : ℤ, ∀ y : (v.adicCompletion E)ˣ, Valued.v (y : v.adicCompletion E) = WithZero.exp n → f y = 1 := by
    intro n
    induction n using Int.induction_on with
    | zero => exact fun y hy => hu y (by show Valued.v _ = 1; rw [hy, WithZero.exp_zero])
    | succ n ih =>
      intro y hy
      have h1 : f (y * p) = 1 := ih _ (by
        rw [Units.val_mul, map_mul, hy, hpv, ← WithZero.exp_add]
        congr 1
        ring)
      rwa [map_mul, hfp, mul_one] at h1
    | pred n ih =>
      intro y hy
      have h1 : f (y * p⁻¹) = 1 := ih _ (by
        rw [Units.val_mul, map_mul, hy, Units.val_inv_eq_inv_val, map_inv₀, hpv, ← WithZero.exp_neg,
          ← WithZero.exp_add]
        congr 1
        ring)
      rwa [map_mul, map_inv, hfp, inv_one, mul_one] at h1
  have h0 : Valued.v (x : v.adicCompletion E) ≠ 0 := by simp
  exact key _ x (WithZero.exp_log h0).symm

variable {Ω : Type} [Field Ω] [Algebra E Ω]

theorem unif_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ha' : IsGlobalArtin art')
    {B : Type} [Group B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E))
    (hu' : ∀ y, IsUnitAt v y → χ (art' (localIdele E v y)) = 1) (x : (v.adicCompletion E)ˣ) (hx : IsUnifAt v x) :
    χ (art (localIdele E v x)) = χ (art' (localIdele E v x)) := by
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω v
  obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
  obtain ⟨y, hy, e'⟩ := (ha'.frob v A hA _).mpr ⟨σ, hσ, e⟩
  have hxy : IsUnitAt v (x * y⁻¹) := by
    show Valued.v _ = 1
    have hy0 : Valued.v (y : v.adicCompletion E) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hx, ← hy, mul_inv_cancel₀ hy0]
  have h2 : localIdele E v x = localIdele E v (x * y⁻¹) * localIdele E v y := by
    rw [← map_mul, inv_mul_cancel_right]
  conv_rhs => rw [h2, map_mul, map_mul, hu' _ hxy, one_mul, e']

end GlobalTheory.ArtinUniq

namespace GlobalTheory.ArtinUniq

variable {E : Type} [Field E] [NumberField E]

theorem eq_infPart {B : Type} [CommGroup B] (D : Ideles E →* B) (hD : IsOpen (D.ker : Set (Ideles E)))
    (hloc : ∀ v x, D (localIdele E v x) = 1) (x : Ideles E) :
    D x = D (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E x)) := by
  have hnhds : {z : Ideles E | D z = D x} ∈ nhds x := by
    have e : {z : Ideles E | D z = D x} = (fun z => x⁻¹ * z) ⁻¹' (D.ker : Set (Ideles E)) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
      rw [inv_mul_eq_one, eq_comm]
    rw [e]
    exact ((continuous_const.mul continuous_id).isOpen_preimage _ hD).mem_nhds (by simp)
  obtain ⟨T, hT⟩ := ((GlobalTheory.HeckeSplit.tendsto_truncIdele x).eventually hnhds).exists
  have h1 : ∀ v ∈ T, D (HeckeValGen.localIdele E v (GlobalTheory.HeckeSplit.finPart E v x)) = 1 := fun v _ => hloc v _
  rw [← show D (GlobalTheory.HeckeSplit.truncIdele x T) = D x from hT, GlobalTheory.HeckeSplit.truncIdele, map_mul, map_prod,
    Finset.prod_eq_one h1, mul_one]

theorem eq_one_of_local {B : Type} [CommGroup B] (D : Ideles E →* B) (hD : IsOpen (D.ker : Set (Ideles E)))
    (hdiag : ∀ k : Eˣ, D (diagUnits E k) = 1) (hinf : ∀ y ∈ infConn E, D y = 1)
    (hloc : ∀ v x, D (localIdele E v x) = 1) : D = 1 := by
  ext x
  rw [eq_infPart D hD hloc x, MonoidHom.one_apply]
  set y := GlobalTheory.HeckeSplit.infPart E x
  let C := Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ
  have hopen : IsOpen ((fun z => y⁻¹ * z) ⁻¹' (C : Set (InfiniteAdeleRing E)ˣ)) :=
    (continuous_const.mul continuous_id).isOpen_preimage _ (isOpen_connectedComponentOfOne_inf E)
  obtain ⟨k, hk⟩ := (denseRange_units_inf E).exists_mem_open hopen ⟨y, by simp [C.one_mem]⟩
  set kinf : (InfiniteAdeleRing E)ˣ := Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k with hkinf
  have hk' : y⁻¹ * kinf ∈ C := hk
  have h1 : D (GlobalTheory.HeckeSplit.infIdele E kinf) = 1 := by
    have h := eq_infPart D hD hloc (diagUnits E k)
    have e : GlobalTheory.HeckeSplit.infPart E (diagUnits E k) = kinf := Units.ext rfl
    rw [e, hdiag k] at h
    exact h.symm
  have h2 : D (GlobalTheory.HeckeSplit.infIdele E (y⁻¹ * kinf)) = 1 := hinf _ ⟨_, hk', rfl⟩
  have e : y = kinf * (y⁻¹ * kinf)⁻¹ := by group
  rw [e, map_mul, map_inv, map_mul, map_inv, h1, h2, inv_one, mul_one]

end GlobalTheory.ArtinUniq

namespace GlobalTheory.ArtinUniq

theorem val_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem globalArtin_unique : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art art' : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art →
    GlobalTheory.HeckeGal.IsGlobalArtin art' → art = art' := by
  intro E Ω _ _ _ _ _ art art' ha ha'
  classical
  ext x
  rw [← div_eq_one]
  refine GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  have hker : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → IsOpen ((χ.comp a).ker : Set (Ideles E)) := by
    intro a h
    have e : ((χ.comp a).ker : Set (Ideles E)) = a ⁻¹' U := by
      ext y
      simp [χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [e]
    exact hU.preimage h.quot.continuous
  have hdiag : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → ∀ k : Eˣ, a (diagUnits E k) = 1 := by
    intro a h k
    have hk : diagUnits E k ∈ a.ker := by
      rw [h.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hinf : ∀ a : Ideles E →* Gab E Ω, IsGlobalArtin a → ∀ y ∈ infConn E, a y = 1 := by
    intro a h y hy
    have hk : y ∈ a.ker := by
      rw [h.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hy)
    exact hk
  let ψ : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  let ψ' : Ideles E →* Gab E Ω ⧸ U := χ.comp art'
  let D : Ideles E →* Gab E Ω ⧸ U := ψ / ψ'
  let V : Subgroup (Ideles E) := ψ.ker ⊓ ψ'.ker
  have hV : IsOpen (V : Set (Ideles E)) := (hker art ha).inter (hker art' ha')
  have hDV : ∀ z ∈ V, D z = 1 := fun z hz => by
    show ψ z / ψ' z = 1
    rw [MonoidHom.mem_ker.mp hz.1, MonoidHom.mem_ker.mp hz.2, div_one]
  have hDo : IsOpen (D.ker : Set (Ideles E)) := Subgroup.isOpen_mono (fun z hz => hDV z hz) hV
  have hDd : ∀ k : Eˣ, D (diagUnits E k) = 1 := fun k => by
    show χ (art _) / χ (art' _) = 1
    rw [hdiag art ha, hdiag art' ha', map_one, div_one]
  have hDi : ∀ y ∈ infConn E, D y = 1 := fun y hy => by
    show χ (art _) / χ (art' _) = 1
    rw [hinf art ha y hy, hinf art' ha' y hy, map_one, div_one]
  obtain ⟨S, M, -, hSu, hSc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E V hV ∅

  have hgood : ∀ v ∉ S, ∀ z, D (localIdele E v z) = 1 := fun v hv z => by
    refine eq_one_of_unit_unif v (D.comp (localIdele E v)) (fun y hy => hDV _ (hSu v hv y hy)) (fun y hy => ?_) z
    show ψ _ / ψ' _ = 1
    rw [div_eq_one]
    exact unif_eq ha ha' χ v (fun y' hy' => MonoidHom.mem_ker.mp (hSu v hv y' hy').2) y hy

  have hbad : ∀ v ∈ S, ∀ z, D (localIdele E v z) = 1 := fun v hv z => by
    have ho : IsOpen ((D.comp (localIdele E v)).ker : Set (v.adicCompletion E)ˣ) :=
      hDo.preimage (GlobalTheory.Mem.UnrAe.continuous_localIdele v)
    have ho1 : IsOpen (((1 : (v.adicCompletion E)ˣ →* Gab E Ω ⧸ U)).ker : Set (v.adicCompletion E)ˣ) := by
      rw [MonoidHom.ker_one]
      exact isOpen_univ
    refine GlobalTheory.units_adicCompletion_hom_ext E v _ (D.comp (localIdele E v)) 1 ho ho1 (fun c => ?_) z
    rw [MonoidHom.one_apply, MonoidHom.comp_apply, ← locUnit_apply]
    let m : ℕ := (WithZero.log (v.valuation E (c : E))).natAbs
    obtain ⟨a, hap, hapos⟩ :=
      GlobalTheory.FinPlaceApproxPos.approxpos_target E S (fun u => if u = v then (c : E) else 1) (M + 1 + m)
    have haW : v.valuation E (a - c) ≤ WithZero.exp (-(((M + 1 : ℕ) : ℤ) + m)) := by
      have := hap v hv
      rw [if_pos rfl] at this
      exact val_le_of_le v this (by push_cast; omega)
    have hz : v.valuation E (a / c - 1) ≤ WithZero.exp (-((M + 1 : ℕ) : ℤ)) :=
      val_div_sub_one_le v c.ne_zero le_rfl haW
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
      push_cast at hz
      omega
    let au : Eˣ := Units.mk0 a ha0
    let q : Eˣ := au / c
    have hq : (q : E) = a / c := by simp [q, au]
    have hqV : locUnit E v q ∈ V := hSc v hv q (by rw [hq]; exact val_le_of_le v hz (by push_cast; omega))
    have hprod := GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos E _ D hDo hDd hDi au (fun φ => hapos φ) S
      (fun u hu => by rw [locUnit_apply]; exact hgood u hu _)
    rw [Finset.prod_eq_single_of_mem v hv (fun u hu hne => hDV _ (hSc u hu au (by
      have := hap u hu
      rw [if_neg hne] at this
      exact val_le_of_le u this (by push_cast; omega))))] at hprod
    have e : au = c * q := by simp [q]
    rw [e, map_mul, map_mul, hDV _ hqV, mul_one] at hprod
    exact hprod
  have hD : D = 1 := eq_one_of_local D hDo hDd hDi fun v z => by
    by_cases hv : v ∈ S
    · exact hbad v hv z
    · exact hgood v hv z
  have h1 : χ (art x / art' x) = 1 := by
    rw [_root_.map_div]
    exact DFunLike.congr_fun hD x
  exact (QuotientGroup.eq_one_iff _).mp h1

end GlobalTheory.ArtinUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Gen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ), FinLike R i t f ∧ φ = R.ωP i t (1, g) f}

def TypeVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t),
    R.ωP i t (κ, 1) f = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f

def TypeDiff (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∃ f : WO (Vc D i) (Wc D i) → ℂ,
    IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ φ = R.ωP i t (κ, 1) f - (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f}

def IsLifts (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (κ : G → GA D (Vc D i)) : Prop :=
  ∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g)

def avgW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool) (ε : ℤ)
    (κ : G → GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) : WO (Vc D i) (Wc D i) → ℂ :=
  ∑ g, (mirC R i PP a tr ε g * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • R.ωP i t ((κ g)⁻¹, 1) f

def AvgIm (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 ∧ ∃ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
    ∃ κ : G → GA D (Vc D i), IsLifts R i t κ ∧ ∃ f : WO (Vc D i) (Wc D i) → ℂ,
      IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ φ = avgW R i t PP a tr ε κ f}

def Clean (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ κ : G → GA D (Vc D i), IsLifts R i t κ → avgW R i t PP a tr ε κ f = 0

section ThetaAlg

variable {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D}

theorem heisO_add' (u : WO S T') (f g : WO S T' → ℂ) : heisO ψ S T' u (f + g) = heisO ψ S T' u f + heisO ψ S T' u g := by
  funext w; simp only [heisO, Pi.add_apply]; ring

theorem theta_add {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    IsThetaFunO ψ S T' (f + g) := {
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    rw [heisO_add', hU u hu.1 hi, hU' u hu.2 hi]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem theta_smul (c : ℂ) {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) : IsThetaFunO ψ S T' (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T' u (c • f) = c • heisO ψ S T' u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w) }

theorem theta_sub {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    IsThetaFunO ψ S T' (f - g) := by
  have e : f - g = f + (-1 : ℂ) • g := by funext w; simp [sub_eq_add_neg]
  rw [e]
  exact theta_add hf (theta_smul (-1) hg)

theorem theta_sum {ι : Type} (s : Finset ι) (u : ι → WO S T' → ℂ)
    (f₀ : WO S T' → ℂ) (h₀ : IsThetaFunO ψ S T' f₀) (hu : ∀ k ∈ s, IsThetaFunO ψ S T' (u k)) :
    IsThetaFunO ψ S T' (∑ k ∈ s, u k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := theta_smul (0 : ℂ) h₀
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact theta_add (hu a (Finset.mem_insert_self _ _)) (ih fun k hk => hu k (Finset.mem_insert_of_mem hk))

end ThetaAlg

end GlobalTheory.DownLift.GenFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeInvariantUnderLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HLatLevel

theorem hLat_mul_lev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (y k : Bridge.Gf V), k ∈ (levEnv V β L).J → Bridge.hLat V (y * k) = Bridge.hLat V y := by
  intro D V β Λ hΛ L y k hk
  have h : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ lev D.sp.cm V.gram β (Lev.flag1L L) := hk
  have hq : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ St β := parLev_St h.1
  have hf : (1 : Bridge.Gf V).1 = Formalism.UG.bc (inclR (F := D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) (1 : GL (Fin V.rank) D.host.E) := by
    rw [map_one]; exact OneMemClass.coe_one _
  have e := GlobalTheory.HLatMove.hLat_mul hΛ 1 y k 1 hf hq
  rw [one_mul] at e
  rw [e]
  ext x
  simp
end GlobalTheory.HLatLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntLowMul
section
namespace GlobalTheory.LowerIntegralMul

theorem intLow_mul {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (Mp : Formalism.MainNotions.S.Loc.Model F E) {n : ℕ}
    {l l' : Matrix (Fin n) (Fin n) E} (hl : Formalism.MainNotions.S.TieN.IntLow Mp l) (hl' : Formalism.MainNotions.S.TieN.IntLow Mp l') :
    Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := by
  unfold Formalism.MainNotions.S.TieN.IntLow at *
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h1', h2', h3'⟩ := hl'
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h1, h1', mul_one]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [h2' c a h, mul_zero]
      · rw [h2 a c h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge a c with h | h
    · rw [h2 a c h, zero_mul]
    · rw [h2' c b (lt_of_le_of_lt h hab), mul_zero]
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (h3 a c) (h3' c b)

end GlobalTheory.LowerIntegralMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegment
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL

theorem isL_map_tw_of_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  intro k _ _ _ _ _ 𝔪 x χ hχ h
  exact (h.tw χ hχ).of_equiv (x.twEquiv χ hχ)

end GlobalTheory.LocGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst

namespace GlobalTheory.GalOfCusp

def LocalGlobalAboveL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, IsRec h rc →
        wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

end GlobalTheory.GalOfCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingOfEtaleExactDeRhamCrystallineConst
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.TheoremAFinal

theorem integralityFromMetric_of_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ CA CB CK C : ℝ, 160 ≤ C → ElementDenominator.IntegralityFromMetric D HW F Cm CA CB CK C := by
  intro D HW F Cm CA CB CK C hC
  exact Formalism.MainNotions.N.Ln34.integrality_from_metric_of_large_constant D HW F Cm CA CB CK C hC
    (fun l _ K s LL hG T₀ T₁ T₂ ι π h => GlobalTheory.LatExact.W_exact D HW F l K s LL hG T₀ T₁ T₂ ι π h)
    (GlobalTheory.CrysDdR.finrank_DdRE_of_isCrys D) (GlobalTheory.NL.IotaLetterRank.finrank_iota_letter D HW F Cm)

end GlobalTheory.TheoremAFinal
end

