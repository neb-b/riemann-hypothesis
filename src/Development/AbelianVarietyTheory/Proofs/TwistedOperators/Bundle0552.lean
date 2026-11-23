module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0467
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowRealAverageHoweDualityFockComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem halfInd_isSBHalf {S T : HSp D} (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (halfInd e Λ) := by
  refine ⟨fun x hx => ?_, 1, one_pos, fun u hu hu' x => ?_, fun x hx => ?_⟩
  · by_contra h; exact hx (if_neg fun h' => h h'.2)
  · rw [one_smul]
    have h1 : IsHalf e (x + u) ↔ IsHalf e x := forall₂_congr fun i j => by
      rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]
    exact halfInd_congr (and_congr (AddSubgroup.add_mem_cancel_right _ hu) h1)
  · rw [one_smul]; by_contra h; exact hx (if_neg fun h' => h h'.1)

theorem om_base_law {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) {h : GA D T}
    (hh : SuppAt e T h) :
    ∃ c : ℂ, om (1, h) f₀ = c • Tm fun x => halfInd e (latO S T ΛS ΛT fun _ => True) (actO S T 1⁻¹ h⁻¹ x) := by
  have he' : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have key := GlobalTheory.SplitLinear.splitLinearModel D ψ S T χS χT om hW ΛS ΛT hS hT P e he f₀ hf hv 1 one_ne_zero Tm hTm 1 h
    (GlobalTheory.SplitLinear.suppAt_one e S) hh _ _ (GlobalTheory.VecInv.isDetAt_detAt e he' S 1) (GlobalTheory.VecInv.isDetAt_detAt e he' T h)
    _ (halfInd_isSBHalf e _)
  have h0 : Tm (halfInd e (latO S T ΛS ΛT fun _ => True)) = f₀ := by simpa using hTm.vac
  rw [h0] at key
  refine ⟨(splitFacO χS χT (GlobalTheory.VecInv.detAt e he' S 1) (GlobalTheory.VecInv.detAt e he' T h) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac S T (GlobalTheory.VecInv.detAt e he' S 1) (GlobalTheory.VecInv.detAt e he' T h) : ℂ), key.trans ?_⟩
  rw [← map_smul]
  rfl

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem compAt_fin {θ : InfFam D} {V : HSp D} {h : GA D V} (hh : h ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = 1 := by
  have h1 : Formalism.UG.bc (infPart D) (matHom V h) = 1 := (GlobalTheory.UnitaryIdemCut.mem_GfC_iff V h).1 hh
  have h2 := congrArg Units.val h1
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [compAt, Matrix.map_apply]
  have h4 : infPart D (Formalism.L2.Theta.mt V h i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := h3
  rw [h4, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem actO_one_one {S T : HSp D} (u : WO S T) : actO S T 1 1 u = u := by
  simp [actO, GlobalTheory.AdelicLatMove.mt_one]

theorem om_keep_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (kS : S.SigOK) (kT : T.SigOK) {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f)
    {h : GA D T} (hh : h ∈ GfC T)
    (hk : ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T 1 h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    ∃ c : ℂ, om (1, h) f = c • f := by
  have hf' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ 1 h
    (fun τ => by rw [compAt_fin (one_mem _) τ, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_fin hh τ, Matrix.mul_one, Matrix.one_mul])
    (fun u => ⟨fun hu => ⟨actO S T 1 h⁻¹ u, (hk _).2 (by rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one]; exact hu),
        by rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one]⟩,
      fun ⟨u₀, hu₀, e⟩ => e ▸ (hk u₀).1 hu₀⟩) f hf
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hf.1 hθ S T sS sT kS kT cS cT ΛS ΛT hS hT f _ hf hf'
  exact ⟨c, hc⟩

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem exists_cut_hom (V : HSp D) (r : AF D.host.F)
    (hb : algebraMap (AF D.host.F) (AE D) r * algebraMap (AF D.host.F) (AE D) r = algebraMap (AF D.host.F) (AE D) r) :
    ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) r • Formalism.L2.Theta.mt V g +
      (1 - algebraMap (AF D.host.F) (AE D) r) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  obtain ⟨κ, hκ⟩ := GlobalTheory.UnitaryIdemCut.exists_cutHA (AF D.host.F) D.sp.cm.sig V.gram r hb
  refine ⟨κ, fun g => ?_⟩
  have := congrArg Units.val (hκ g)
  rw [GlobalTheory.UnitaryIdemCut.cutGL_val] at this
  exact this

theorem actO_cut_half {S T : HSp D} {b e : AE D} (hbe : b * e = 0) {g : GA D T}
    {M : Matrix (Fin T.rank) (Fin T.rank) (AE D)}
    (hg : Formalism.L2.Theta.mt T g = b • M + (1 - b) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) {y : WO S T}
    (hy : IsHalf e y) : actO S T 1 g y = y := by
  have hby : ∀ i j, b * y i j = 0 := fun i j => by rw [← hy i j, ← mul_assoc, hbe, zero_mul]
  have h1 : actO S T 1 g y = (HMul.hMul (Formalism.L2.Theta.mt T g) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :
      Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    simp [actO, GlobalTheory.AdelicLatMove.mt_one]
  rw [h1, hg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_eq_zero fun k _ => by rw [mul_left_comm, hby, mul_zero], zero_add, sub_mul, one_mul,
    hby, sub_zero]

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem cut_mul_cut {n : Type} [Fintype n] [DecidableEq n] {a : AE D} (ha : a * a = a) (M : Matrix n n (AE D)) :
    (a • M + (1 - a) • (1 : Matrix n n (AE D))) * ((1 - a) • M + (1 - (1 - a)) • (1 : Matrix n n (AE D))) = M := by
  have h0 : a * (1 - a) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
  have h0' : (1 - a) * a = 0 := by rw [mul_comm, h0]
  have h1 : (1 - a) * (1 - a) = 1 - a := by rw [sub_mul, one_mul, h0, sub_zero]
  rw [sub_sub_cancel]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
  simp only [smul_add, smul_smul, h0, h0', ha, h1, zero_smul, zero_add, add_zero]
  rw [← add_smul, sub_add_cancel, one_smul]

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_cut_pair (V : HSp D) {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) :
    ∃ κe κo : GA D V →* GA D V, (∀ g, g = κe g * κo g) ∧ (∀ g, SuppAt e V (κe g)) ∧ (∀ g ∈ GfC V, κo g ∈ GfC V) ∧
      (∀ g, Formalism.L2.Theta.mt V (κo g) = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V g +
        (e + cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      ∀ (S : HSp D) g (y : WO S V), IsHalf e y → actO S V 1 (κo g) y = y := by
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hec : cA D e * e = 0 := by rw [mul_comm]; exact hc
  obtain ⟨r, hr⟩ := GlobalTheory.PlaceModelSum.exists_add_conj e
  have hr1 : algebraMap (AF D.host.F) (AE D) (1 - r) = 1 - algebraMap (AF D.host.F) (AE D) r := by
    simp only [map_sub, map_one]
  have hrr : algebraMap (AF D.host.F) (AE D) r * algebraMap (AF D.host.F) (AE D) r =
      algebraMap (AF D.host.F) (AE D) r := by
    rw [hr, add_mul, mul_add, mul_add, he, hce, hc, hec, add_zero, zero_add]
  have hrr' : algebraMap (AF D.host.F) (AE D) (1 - r) * algebraMap (AF D.host.F) (AE D) (1 - r) =
      algebraMap (AF D.host.F) (AE D) (1 - r) := by
    rw [hr1, sub_mul, mul_sub, mul_sub, hrr, mul_one, one_mul, mul_one, sub_self, sub_zero]
  have hbe0 : algebraMap (AF D.host.F) (AE D) (1 - r) * e = 0 := by
    rw [map_sub, map_one, hr, sub_mul, add_mul, he, hec, one_mul, add_zero, sub_self]
  have hbe : (1 - algebraMap (AF D.host.F) (AE D) r) * e = 0 := by rw [← hr1]; exact hbe0
  obtain ⟨κe, hκe⟩ := exists_cut_hom V r hrr
  obtain ⟨κo, hκo⟩ := exists_cut_hom V (1 - r) hrr'
  rw [hr1] at hκo
  have hκo' : ∀ g, Formalism.L2.Theta.mt V (κo g) = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V g +
      (e + cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := fun g => by
    rw [hκo, ← hr, sub_sub_cancel]
  refine ⟨κe, κo, fun g => ?_, fun g i j => ?_, fun g hg => ?_, hκo', fun S g y hy => ?_⟩
  · refine Subtype.ext (Units.ext ?_)
    change Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V (κe g * κo g)
    rw [GlobalTheory.AdelicLatMove.mt_mul, hκe, hκo, cut_mul_cut hrr]
  · have e1 : Formalism.L2.Theta.mt V (κe g) - 1 = algebraMap (AF D.host.F) (AE D) r • (Formalism.L2.Theta.mt V g - 1) := by
      rw [hκe, smul_sub, sub_smul, one_smul]; abel
    rw [e1, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← hr, hrr]
  · have e1 : matHom V (κo g) = GlobalTheory.UnitaryIdemCut.cutGL _ hrr' (matHom V g) :=
      Units.ext (by rw [GlobalTheory.UnitaryIdemCut.cutGL_val, hr1]; exact hκo g)
    rw [GlobalTheory.UnitaryIdemCut.mem_GfC_iff, e1]
    exact GlobalTheory.UnitaryIdemCut.bc_cutGL_eq_one _ _ _ ((GlobalTheory.UnitaryIdemCut.mem_GfC_iff _ _).1 hg)
  · exact actO_cut_half hbe (hκo g) hy

theorem halfInd_move {S T : HSp D} {e : AE D} (Λ : AddSubgroup (WO S T)) {h he ho : GA D T} (hs : h = he * ho)
    (hfix : ∀ w, IsHalf e w → actO S T 1 ho w = w) (hfix' : ∀ w, IsHalf e w → actO S T 1 ho⁻¹ w = w) (x : WO S T) :
    halfInd e Λ (actO S T 1⁻¹ he⁻¹ x) = halfInd e Λ (actO S T 1⁻¹ h⁻¹ x) := by
  apply halfInd_congr
  have e0 : actO S T 1⁻¹ (ho⁻¹ * he⁻¹) x = actO S T 1 ho⁻¹ (actO S T 1⁻¹ he⁻¹ x) := by
    rw [← GlobalTheory.SplitLinear.actO_mul, one_mul]
  rw [hs, mul_inv_rev, e0]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hfix' _ h2]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have e2 := hfix _ h2
    rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one] at e2
    rw [← e2] at h1 h2
    exact ⟨h1, h2⟩

end GlobalTheory.VacMoveLow

namespace GlobalTheory.ExpansionInvariance

theorem vac_move_low : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      ∃ c : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c • Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  intro D T L sc G W U S t htU Φ β j hj k hk e he Tm hTm
  have hIn : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hDef : GlobalTheory.FunObj.DefPair D.R.m (Pair.top t j : Pair T) := by
    show j + 1 ≤ D.R.m
    omega
  have hW := W.om_is _ hIn
  have hvac := S.Z.vac_is _ hDef
  have hSd : IsSelfDualC (G.pS (.top t j : Pair T)) (S.N.latS (.top t j)) :=
    S.N.selfDual (X := .top j) (show j ≤ D.R.m by omega)
  have hTd : IsSelfDualC (G.pT (.top t j : Pair T)) (S.N.latT (.top t j)) :=
    S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have kS : (G.pS (.top t j : Pair T)).SigOK := (G.isV (X := .top j) (show j ≤ D.R.m by omega) (by simp)).sigOK
  have kT : (G.pT (.top t j : Pair T)).SigOK :=
    (G.isV (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) (by simp)).sigOK
  have he' : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  obtain ⟨κe, κo, hsplit, hSupp, hFin, hmt, hfix⟩ := GlobalTheory.VacMoveLow.exists_cut_pair (G.V (.top (j + 1))) he' he.2
  set h : GA D (G.V (.top (j + 1))) := (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
    GA D (G.V (.top (j + 1)))) with hh_def
  have hoLat := GlobalTheory.CutStdLat.keep_stdLatO S htU j hj k hk e he (κo h) (hmt h)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.VacMoveLow.om_keep_vac hW W.θ_is kS kT
    (fun τ => W.cart_is (.top j) (show j ≤ D.R.m by omega) τ)
    (fun τ => W.cart_is (.top (j + 1)) (show j + 1 ≤ D.R.m by omega) τ) hSd hTd hvac
    (hFin h ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2) hoLat
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.VacMoveLow.om_base_law hW hSd hTd he hvac.2.theta hvac.2.lat hTm (hSupp h)
  refine ⟨c₁ * c₂, ?_⟩
  rw [show ((1 : GA D (G.pS (.top t j : Pair T))), h) = ((1 : GA D (G.pS (.top t j : Pair T))), κe h) * (1, κo h) by
    rw [Prod.mk_mul_mk, mul_one, ← hsplit], map_mul, Module.End.mul_apply, hc₁, map_smul, hc₂, smul_smul]
  congr 2
  funext x
  refine GlobalTheory.VacMoveLow.halfInd_move _ (hsplit h) (fun w hw => hfix _ h w hw) (fun w hw => ?_) x
  rw [← map_inv]
  exact hfix _ h⁻¹ w hw

end GlobalTheory.ExpansionInvariance
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumLocalFunctionsEqPureTensorScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch

open GlobalTheory.BigDat GlobalTheory.WeilM


set_option maxHeartbeats 1600000 in
theorem datum_placesA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ f₀, IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) →
    ∀ ι : ∀ w : Pl D.host.E, ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
      (Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ),
    (∀ w ∈ locPl G t, IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) (ι w)) →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ε, IsIdemSum ε (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Ψ (τ : TotT G (routeBig t i j)),
      (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Ψ w)) →
      HasLocal B t ε (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
        (IsLocVec W (.chi i (j + 1)) ε (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) ε (ρ.vT (i + 1) j)) τ Ψ →
      ∀ φ, IsFinPart Γ.M X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (s • f₀) φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M _ e Bs Γ X om om' h hT hti f₀ hdat ι hι
  classical
  have h₁ := ρ.vX_is i (j + 1) i.2 j.2
  have h₂ := ρ.vT_is t (i + 1) j i.2 j.2
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨hadd, -, -⟩ := GlobalTheory.BigDat.ThBox.thetaPt_box W M t i j e Bs Γ X om om' h hT
  have hf : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) = box e (ρ.vX i (j + 1)) (ρ.vT (i + 1) j) := by
    funext u
    have := hdat.2 u
    exact this.trans ((Finsupp.sum_single_index (zero_mul _)).trans (one_mul _))
  obtain ⟨hid, hsumid⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := fun w hw => GlobalTheory.BigDat.halves_split hL W i j e Γ h.JW h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := GlobalTheory.BigDat.mixCo_spec B t i j e
  have hv := fun w hw => lagr_vac (hι w hw) (hG.vac _).1 (hG.vac _).2.1 (latPt e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => GlobalTheory.BigDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (GlobalTheory.BigDat.latPt_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 (hh w hw).2.2.2.1
  set c := ∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0 with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hv w hw).1
  refine ⟨c, hc0, ?_⟩
  intro ε hε n Ψ τ _ hloc φ hφ hΨ
  obtain ⟨φ₁, φ₂, hmem, hsum⟩ := hloc
  have sW := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  obtain ⟨T₁, hT₁⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg sW)
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd _ ε hε _ h₁.2.theta h₁.2.lat).1
  obtain ⟨T₂, hT₂⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd sW _ ε hε _ h₂.2.theta h₂.2.lat).1
  obtain ⟨g0, g1, g2⟩ := GlobalTheory.BigDat.boxGraph_graph_heis hL W i j e Γ h.JW h.JWW ε _ hε _ _ T₁ T₂ hT₁ hT₂
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  have hb : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f₀) Γ.M.vac) = c • box e (ρ.vX i (j + 1)) (ρ.vT (i + 1) j) := by
    rw [← hf]
    exact funext fun u => (congrArg (thetaPt Γ W.ψ · u) (funext fun _ => mul_assoc _ _ _)).trans (thetaPt_smul _ _ _ _ u)
  let R : Submodule ℂ ((Pt G i j → ℂ) × ((Ix G i j → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ schA D.host.F _ ∧ (p.1, thetaPt Γ W.ψ p.2) ∈ boxGraph e ε T₁ T₂}
      zero_mem' := ⟨zero_mem _, by
        have : thetaPt Γ W.ψ 0 = 0 := funext fun u => by simpa using thetaPt_smul Γ W.ψ 0 0 u
        rw [Prod.snd_zero, this]; exact zero_mem _⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, by
        rw [Prod.snd_add, hadd _ hp.1 _ hq.1]; exact add_mem hp.2 hq.2⟩
      smul_mem' := fun a p hp => ⟨Submodule.smul_mem _ a hp.1, by
        rw [Prod.smul_snd, show thetaPt Γ W.ψ (a • p.2) = a • thetaPt Γ W.ψ p.2 from funext (thetaPt_smul _ _ _ _)]
        exact Submodule.smul_mem _ a hp.2⟩ }
  have hA : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (atPl w 1), x ∈ mixHalf e ε := fun w hw x hx =>
    ⟨isHalf_mono (hεw w hw) hx.1, isHalf_mono (hεw w hw) hx.2⟩
  have hA' : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (cA D (atPl w 1)), x ∈ mixHalf e (cA D ε) := fun w hw x hx =>
    have : cA D ε * cA D (atPl w 1) = cA D (atPl w 1) := by rw [← RingHom.map_mul, hεw w hw]
    ⟨isHalf_mono this hx.1, isHalf_mono this hx.2⟩
  have hbase : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, ι w (Γ.M.vac _) (mixCo B t e w u)) =
      c • box e (halfInd ε (latV G i j)) (halfInd ε (latW G i j)) := by
    funext u
    rw [Pi.smul_apply, smul_eq_mul, box, halfInd, halfInd]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ ((hco w).2.2.1 u).symm).trans ((hv w hw).2 _ ((hh w hw).2.2.2.2 u).1)]
      by_cases hl : mapV e u ∈ latV G i j ∧ mapW e u ∈ latW G i j
      · rw [if_pos ⟨hl.1, hu.1⟩, if_pos ⟨hl.2, hu.2⟩, mul_one, mul_one]
        exact Finset.prod_congr rfl fun w hw => Set.indicator_of_mem (((hh w hw).2.2.2.2 u).2.2 hl.1 hl.2) _
      · have : ∃ w ∈ locPl G t, ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u) ∉ latPt e (w.under (𝓞 D.host.F)) := by
          by_contra! hall
          exact hl ⟨mem_of_sum_smul (hεs ▸ hu.1) fun w hw => (mapV_ofMaps e _ ▸ (hall w hw).2.1 :),
            mem_of_sum_smul (hεs ▸ hu.2) fun w hw => (mapW_ofMaps e _ ▸ (hall w hw).2.2 :)⟩
        obtain ⟨w, hw, hn⟩ := this
        rw [Finset.prod_eq_zero hw (Set.indicator_of_notMem hn _)]
        rcases not_and_or.1 hl with hl | hl
        · rw [if_neg fun h => hl h.1, zero_mul, mul_zero]
        · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.1, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      rcases not_and_or.1 hu with hl | hl
      · rw [if_neg fun h => hl h.2, zero_mul, mul_zero]
      · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.2, mul_zero, mul_zero]
  have hR := GlobalTheory.InductLagr.rel_of_vac Γ.M W.ψ hstd hG (locPl G t) (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) _
    (fun w => mixHalf e (atPl w 1)) (fun w => mixHalf e (cA D (atPl w 1))) (mixCo B t e) ι (halfPt e ε) R (c • f₀)
    (fun w hw => hι w hw) (fun w hw u hu => ⟨(hh w hw).1 u hu, mem_halfPt.2 (hA w hw u hu)⟩) (fun w hw => (hh w hw).2.1)
    (fun w hw => (hh w hw).2.2.1) (fun w _ x _ u => (hco w).1 u x)
    (fun w _ w' _ hne x hx u => by rw [(hco w').1, (hco w').2.2.2 w hne.symm x hx, add_zero])
    (fun w hw u => ⟨_, ((hh w hw).2.2.2.2 u).1, (hco w).2.2.1 u, ((hh w hw).2.2.2.2 u).2.1⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g1 x (hA w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g2 x (hA' w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    ⟨(isFinPart_vac hG ∅).fam.mem hG _, by
      have := (boxGraph e ε T₁ T₂).smul_mem c (Submodule.subset_span
        ⟨_, _, GlobalTheory.isSBHalf_halfInd ε _, GlobalTheory.isSBHalf_halfInd ε _, rfl⟩)
      rw [(congrArg T₁ (one_smul ℂ _).symm).trans hT₁.vac, (congrArg T₂ (one_smul ℂ _).symm).trans hT₂.vac] at this
      show (_, thetaPt Γ W.ψ _) ∈ _
      rw [hbase, hb]
      exact this⟩
    φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.2.2.1 v).1 hm; hv w hw e
  have hτ : (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)) ∈ boxGraph e ε T₁ T₂ :=
    sum_mem fun d hd => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, (hmem d hd).1.1, (hmem d hd).2.1, by
      rw [← (hmem d hd).1.2.2 T₁ hT₁, ← (hmem d hd).2.2.2 T₂ hT₂]⟩)
  have hfst : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, ι w (φ _) (mixCo B t e w u)) =
      (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)).1 := by
    funext u
    rw [Prod.fst_sum, Finset.sum_apply]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw => congrFun (hΨ w hw) _]
      exact (hsum _ _ hu.1 hu.2).symm
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      refine (Finset.sum_eq_zero fun d hd => mul_eq_zero_of_right _ ?_).symm
      by_contra hne
      exact hu ⟨(hmem d hd).1.1.1 _ (left_ne_zero_of_mul hne), (hmem d hd).2.1.1 _ (right_ne_zero_of_mul hne)⟩
  refine ⟨hR.1, fun u => ?_⟩
  have := g0 _ (by
    have := sub_mem hR.2 hτ
    rwa [← Prod.mk.eta (p := Finset.sum _ _), Prod.mk_sub_mk, ← hfst, sub_self] at this)
  have := congrFun (sub_eq_zero.1 this) u
  rw [Prod.snd_sum, Finset.sum_apply] at this
  exact this

end GlobalTheory.FlipMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorMatrixCoefficientFormula
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.FockCoeffImage

theorem fockCoefficientC : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → FockCoefficientC R F := by
  intro hHM D G _ _ Pl0 T A Ks _ _ _ R F hPM
  intro i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ x hx g hg e e' w w'
  obtain ⟨hne, hth, hcart1, hvac⟩ := _root_.GlobalTheory.LiftFockVac.levVec_fockVac R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ
  have hreal := _root_.GlobalTheory.FockCoefReal.fock_coef_real hHM R F hPM i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ g hg e e' w w'
  obtain ⟨hC, -, -, -, -, hW, hON, -, hPt, -, -⟩ := h
  have hinf : IsInfFam R.θ := hC.models.inf
  have hbM : GlobalTheory.AdelicScalar.realElt R.θ (Wc D i) g ∈ GinfC (Wc D i) := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hy
    exact GlobalTheory.PointAtPlaceHom.atTau_mem _ τ _
  have key := _root_.GlobalTheory.FockCoefSplit.coef_split D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hinf hW μ 𝓧 hμ (fun _ => 1) (R.BV i)
    (cart (R.MW i σ)) BW hcart1 (fun τ => GlobalTheory.Chain.VacVec.cart_isCartanInv _ τ) (fun _ => (Vc D i).rank) (pW D i)
    (fun τ => hC.models.BV i τ) hON f hth hvac (fun Q => hPt Q) 1 (one_mem _) _ hbM 1 (one_mem _) x hx
    (io (PiTensorProduct.tprod ℂ e) w) (io (PiTensorProduct.tprod ℂ e') w')
  rw [one_mul] at key
  change _ * l2 μ 𝓧 f f = l2 μ 𝓧 (ω (1, GlobalTheory.AdelicScalar.realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w)))
    (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) * _ at key
  rw [hreal] at key
  refine mul_right_cancel₀ hne (key.trans ?_)
  ring

end GlobalTheory.FockCoeffImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFourth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaArrowType


open GlobalTheory.Grid in
theorem sigOK_vert {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridPre R) (hG : G.Is) :
    ∀ i j, i ≤ D.R.m → j ≤ D.R.m → (G.V i j).V.SigOK
  | 0, 0, _, _ => D.sp.Y_sig 0
  | 0, j + 1, _, _ => by
    show (row0 R (j + 1)).V.SigOK
    by_cases h : j + 1 < D.R.m
    · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]; exact D.sp.Y_sig _
    · rw [← nodeX_eq_chainVertexAtRowZero_of_ge R h]; exact D.sp.X'_sig
  | i + 1, j, hi, hj => (hG.spaces.vert i j hi hj).sigOK

theorem goodPar_of_node {D : D7} (N : GlobalTheory.Grid.Node D) (hV : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) := by
  obtain ⟨hp, hq⟩ := GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hV (tauE D τ))
  exact ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ,
    GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ), hp, hq⟩

end GlobalTheory.ThetaArrowType
end

