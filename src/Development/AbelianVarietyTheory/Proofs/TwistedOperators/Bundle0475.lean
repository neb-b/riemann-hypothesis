module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeSpanProjectionPreservesFiniteDimInvariantSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

theorem typeSpan_proj_mem {M ι : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (G : Submodule ℂ M)
    (ρ : ι → M →ₗ[ℂ] M) (inv : ι → ι) (hpos : ∀ x ∈ G, x ≠ 0 → 0 < (b x x).re)
    (hherm : ∀ x ∈ G, ∀ y ∈ G, star (b x y) = b y x)
    (_hρG : ∀ i, ∀ x ∈ G, ρ i x ∈ G) (hadj : ∀ i, ∀ x ∈ G, ∀ y ∈ G, b (ρ i x) y = b x (ρ (inv i) y))
    (hproj : ∀ F : Submodule ℂ M, F ≤ G → FiniteDimensional ℂ F →
      ∃ π : M →ₗ[ℂ] M, (∀ x, π x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (π x) f = b x f)
    (Y₀ : Submodule ℂ M) (e : M →ₗ[ℂ] M) (he : ∀ x, e x ∈ typeSpan ρ Y₀ G)
    (he' : ∀ x, ∀ f ∈ typeSpan ρ Y₀ G, b (e x) f = b x f)
    (Y : Submodule ℂ M) (hYf : FiniteDimensional ℂ Y) (hYG : Y ≤ G) (hYρ : ∀ i, ∀ y ∈ Y, ρ i y ∈ Y) :
    ∀ x ∈ Y, e x ∈ Y := by
  intro x hx
  have hzero : ∀ d ∈ G, b d d = 0 → d = 0 := by
    intro d hd h
    by_contra hne
    have := hpos d hd hne
    rw [h] at this
    simp at this
  obtain ⟨π, hπY, hπ⟩ := hproj Y hYG hYf
  have hcomm : ∀ i, ∀ z ∈ G, π (ρ i z) = ρ i (π z) := by
    intro i z hz
    have hdY : π (ρ i z) - ρ i (π z) ∈ Y := Y.sub_mem (hπY _) (hYρ i _ (hπY z))
    have hpair : ∀ y ∈ Y, b (π (ρ i z) - ρ i (π z)) y = 0 := by
      intro y hy
      have h1 : b (π (ρ i z)) y = b (ρ i z) y := hπ _ y hy
      have h2 : b (ρ i z) y = b z (ρ (inv i) y) := hadj i z hz y (hYG hy)
      have h3 : b z (ρ (inv i) y) = b (π z) (ρ (inv i) y) := (hπ z _ (hYρ (inv i) y hy)).symm
      have h4 : b (ρ i (π z)) y = b (π z) (ρ (inv i) y) := hadj i (π z) (hYG (hπY z)) y (hYG hy)
      rw [map_sub, LinearMap.sub_apply, h1, h2, h3, h4, sub_self]
    exact sub_eq_zero.mp (hzero _ (hYG hdY) (hpair _ hdY))
  have hSG : typeSpan ρ Y₀ G ≤ G := typeSpan_le ρ Y₀ G
  have hY1f : FiniteDimensional ℂ (typeSpan ρ Y₀ G ⊓ Y : Submodule ℂ M) :=
    Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨π₁, hπ₁Y, hπ₁⟩ := hproj (typeSpan ρ Y₀ G ⊓ Y) (inf_le_left.trans hSG) hY1f
  have hpS : π₁ x ∈ typeSpan ρ Y₀ G := (hπ₁Y x).1
  have hpY : π₁ x ∈ Y := (hπ₁Y x).2
  have hxp : x - π₁ x ∈ Y := Y.sub_mem hx hpY
  have hle : typeSpan ρ Y₀ G ≤ LinearMap.ker (b (x - π₁ x)) := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [LinearMap.mem_ker]
    have hTw : T w ∈ G := hT.1 ⟨w, hw, rfl⟩
    have hπT : π (T w) ∈ typeSpan ρ Y₀ G ⊓ Y := by
      refine ⟨?_, hπY _⟩
      have hm := map_le_typeSpan ρ (Y₀ := Y₀) (G := G) (π ∘ₗ T) ?_ ?_
      · exact hm ⟨w, hw, rfl⟩
      · rintro _ ⟨v, -, rfl⟩; exact hYG (hπY _)
      · intro i v hv
        simp only [LinearMap.comp_apply]
        rw [hT.2 i v hv, hcomm i _ (hT.1 ⟨v, hv, rfl⟩)]
    have e1 : b (x - π₁ x) (π (T w)) = 0 := by
      rw [map_sub, LinearMap.sub_apply, hπ₁ x _ hπT, sub_self]
    have e2 : b (T w - π (T w)) (x - π₁ x) = 0 := by
      rw [map_sub b (T w) (π (T w)), LinearMap.sub_apply, hπ (T w) _ hxp, sub_self]
    have e3 : b (x - π₁ x) (T w - π (T w)) = 0 := by
      rw [← hherm _ (G.sub_mem hTw (hYG (hπY _))) _ (hYG hxp), e2, star_zero]
    have hsplit : T w = π (T w) + (T w - π (T w)) := by abel
    rw [hsplit, map_add (f := _), e1, e3, add_zero]
  have hd : e x - π₁ x ∈ typeSpan ρ Y₀ G := Submodule.sub_mem _ (he x) hpS
  have hdd : b (e x - π₁ x) (e x - π₁ x) = 0 := by
    have h1 := he' x _ hd
    have h2 := LinearMap.mem_ker.mp (hle hd)
    rw [map_sub b x (π₁ x), LinearMap.sub_apply] at h2
    rw [map_sub b (e x) (π₁ x), LinearMap.sub_apply]
    rw [h1, sub_eq_zero.mp h2, sub_self]
  have h0 := hzero _ (hSG hd) hdd
  rw [sub_eq_zero.mp h0]
  exact hpY

end GlobalTheory.KTypeProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

theorem char_identity {ι : Type} (Pg Q : Finset ι) (a a' d xa xb xd : ι → ℂˣ) (h : ∀ i ∈ Pg, a' i = a i) :
    ((∏ i ∈ Pg, (a i * d i)⁻¹) * ∏ i ∈ Q, xa i * xd i)⁻¹ * ((∏ i ∈ Pg, (a' i)⁻¹) * ∏ i ∈ Q, xb i) =
      (∏ i ∈ Q, (xa i)⁻¹ * xb i) * (1 * (∏ i ∈ Pg, (d i)⁻¹) * ∏ i ∈ Q, xd i)⁻¹ := by
  rw [Finset.prod_congr rfl fun i hi => congrArg (·⁻¹) (h i hi)]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  generalize (∏ i ∈ Pg, a i) = A, (∏ i ∈ Pg, d i) = B, (∏ i ∈ Q, xa i) = C, (∏ i ∈ Q, xb i) = E, (∏ i ∈ Q, xd i) = F
  apply Units.ext
  push_cast
  field_simp

theorem smul_cancel {X : Type} {u v : X → ℂ} {ι : Type} {Q : Finset ι} {x : ι → ℂˣ} {m m' l : ℂˣ} {c : ℂ}
    (h : (∏ i ∈ Q, ((x i : ℂˣ) : ℂ)) • u = c • v) (hc : c = (m : ℂ)⁻¹ * m') (e : m⁻¹ * m' = (∏ i ∈ Q, x i) * l⁻¹) :
    u = (l : ℂ)⁻¹ • v := by
  rw [hc, ← Units.val_inv_eq_inv_val, ← Units.val_mul, e, ← Units.coe_prod, Units.val_mul, mul_smul] at h
  rw [← Units.val_inv_eq_inv_val]
  exact smul_right_injective _ (Units.ne_zero _) h

variable {D : D7}

theorem om_vec {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {Pg Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    (hη : ∃ η, IsEtaTilde D η) (sdS : IsSelfDualC S ΛS) (sdT : IsSelfDualC T ΛT) (frS : IsFrame βS ΛS)
    (frT : IsFrame βT ΛT) (hv : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) :
    ∃ (P : Finset (Pl D.host.E)) (e : AE D) (he : e * e = e), (∀ PP, PP ∈ P ↔ PP ∈ Pg ∨ PP ∈ Q) ∧ IsIdemSum e P ∧
      (UnrOff (e + cA D e) χS → UnrOff (e + cA D e) χT → ∀ (r : ℕ) (hS : r ≤ S.rank) (hT : r ≤ T.rank), T.rank = r →
        ∀ g h, Stab S βS g → Stab T βT h →
        (∀ PP, PP ∈ Pg ∨ PP ∈ Q → redFn βS PP (finE S g) ∈ blockTri (blk2 r)) →
        (∀ PP ∈ Pg, upperLeftBlock hS (redFn βS PP (finE S g)) = upperLeftBlock hT (redFn βT PP (finE T h))) →
        (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hS (redFn βS PP (finE S g)))))⁻¹ *
            ξ PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)) • om (g, h) f =
          ((splitFacO χS χT (detAt e he S g) (detAt e he T h) : Circle) : ℂ) • f) := by
  obtain ⟨hvac, e, he, hth⟩ := hv
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart he
  refine ⟨_, e, hee, fun PP => @Finset.mem_union _ (_) _ _ PP, he, fun u1 u2 r hS hT hr g h sS sT tri same => ?_⟩
  have h0 := _root_.GlobalTheory.VecInv.Vac.stab_vacuum D ψ S T ΛS ΛT χS χT om hW sdS sdT hη βS βT frS frT _ e hee he u1 u2 g h sS sT f₀ hvac.2.theta
    hvac.2.lat
  exact _root_.GlobalTheory.SchrMove.smul_om_eq D ψ S T ΛS ΛT χS χT om hW sdS sdT (cA D e) (by rw [← RingHom.map_mul, hee])
    (GlobalTheory.PlaceVec.infPart_cA hinf) g h (mem_latO_iff frS frT sS.2 sT.2) f₀
    (adjDatum S T βS βT Pg Q ξ (cA D e)) f _ _ hvac.2.theta hth (Circle.coe_ne_zero _) h0
    (_root_.GlobalTheory.AdjDatumMove.adjDatum_actO D S T βS βT Pg Q ξ _ r hS hT hr g h sS.2 sT.2 tri same)

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

theorem levChi_flag_V (i : Fin D.R.m) (t : T0) {κ : GA D (Vc D i)}
    (tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t)) :
    levChi _ (L.βV i) (flagL (L.datVt i t)) κ =
      ((1 * (∏ PP ∈ L.Pg, (L.chi ((i : ℕ) + 1) PP (dBlk (blk2 D.R.r) 1 (redFn (L.βV i) PP (finE (Vc D i) κ))))⁻¹) *
        ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn (L.βV i) PP (finE (Vc D i) κ))) : ℂˣ) : ℂ) := by
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  refine congrArg Units.val (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) rfl)
  · exact extendOne_of_mem _ (Subgroup.mem_top _)
  · refine Finset.prod_congr rfl fun PP h => ?_
    rw [← (_root_.GlobalTheory.VecInv.TwoBlockDet.det_blocks _ _ _ D.R.t (r_le_V i) _).2.1 rV (tg PP h)]
    exact Finset.prod_range_one _

theorem om_lifts (hL : L.Is μ0) (i : Fin D.R.m) (t : T0) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {sS : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : WO (Vc D i) (Wc D i) → ℂ}
    {om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)}
    (hW : IsWeilDatumO ψ (Vc D i) (Wc D i) (L.mu t ((i : ℕ) + 1)) (L.mu t ((i : ℕ) + 1) * L.eta⁻¹) om)
    (hv : IsThPVecOf ψ θ (Vc D i) (Wc D i) sS sT (L.ΛV i) (L.ΛW i) (L.βV i) (L.βW i) L.Pg (L.Q t) (L.xiR t) f₀ f)
    {g0 : G0 L.Pg D.R.r} {κ : GA D (Vc D i)} {κ' : GA D (Wc D i)}
    (hκ : IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) g0 κ) (hκ' : IsLevelLift (Wc D i) (L.βW i) (L.datWp i L.triv) g0 κ') :
    om (κ, κ') f = (levChi _ (L.βV i) (flagL (L.datVt i t)) κ)⁻¹ • f := by
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hη : IsEtaTilde D L.eta := _root_.GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta L.C.isEta _ _ _ hW.resS hW.resT (by
    rw [rV, rW]
    obtain ⟨c, hc⟩ := D.R.t_odd
    exact ⟨D.R.r + c, by omega⟩)
  obtain ⟨P, e, hee, hP, he, hom⟩ := om_vec hW ⟨_, hη⟩ (_root_.GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i))
    (_root_.GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 hv
  obtain ⟨u1, u2⟩ := unrOff_mu hL t i hP he
  have sV : finE (Vc D i) κ ∈ St (L.βV i) := parLev_St hκ.2.1
  have sW : finE (Wc D i) κ' ∈ St (L.βW i) := parLev_St hκ'.2.1
  have tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t) := fun PP h =>
    parLev_g hκ.2.1 h
  have tri : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blk2 D.R.r) := fun PP h =>
    h.elim (fun h => blockTri_blkOf_le _ _ (tg PP h)) fun h => parLev_q hκ.2.1 h
  have same : ∀ PP ∈ L.Pg, upperLeftBlock (r_le_V i) (redFn (L.βV i) PP (finE (Vc D i) κ)) =
      upperLeftBlock (r_le_rank_Wc i) (redFn (L.βW i) PP (finE (Wc D i) κ')) := fun PP h =>
    (congrFun hκ.2.2 ⟨PP, h⟩).trans (congrFun hκ'.2.2 ⟨PP, h⟩).symm
  have h1 := hom u1 (u1.mul u2.inv) _ (r_le_V i) (r_le_rank_Wc i) rW κ κ' ⟨hκ.1, sV⟩ ⟨hκ'.1, sW⟩ tri same
  obtain ⟨aV, haV, hrV⟩ := exists_det_int sV
  obtain ⟨aW, haW, hrW⟩ := exists_det_int sW
  obtain ⟨mV, nV⟩ := mu_val hL t i hP he (detAt e hee _ κ) _ aV _ (isDetAt_detAt e hee _ κ) haV fun PP _ => hrV PP
  obtain ⟨mW, -⟩ := mu_val hL t i hP he (detAt e hee _ κ') _ aW _ (isDetAt_detAt e hee _ κ') haW fun PP _ => hrW PP
  rw [levChi_flag_V i t tg]
  refine smul_cancel h1 (by
    rw [splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, nV, inv_one, mul_one, Circle.coe_mul, Circle.coe_inv,
      mV, mW]) ?_
  refine Eq.trans ?_ (char_identity L.Pg (L.Q t)
    (fun PP => L.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (upperLeftBlock (r_le_V i)
      (redFn (L.βV i) PP (finE (Vc D i) κ)))))
    (fun PP => L.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (redFn (L.βW i) PP (finE (Wc D i) κ')))) _ _ _ _
    fun PP h => by rw [same PP h, (_root_.GlobalTheory.VecInv.TwoBlockDet.det_blocks _ _ _ 0 (r_le_rank_Wc i) _).2.2 rW])
  refine congrArg₂ (· * ·) (congrArg (·⁻¹) (congrArg₂ (· * ·) ?_ ?_)) rfl
  · exact Finset.prod_congr rfl fun PP h => by
      rw [(_root_.GlobalTheory.VecInv.TwoBlockDet.det_blocks _ _ _ 0 (r_le_V i) _).1 (tri PP (Or.inl h)), map_mul]
  · exact Finset.prod_congr rfl fun PP h => by
      rw [(_root_.GlobalTheory.VecInv.TwoBlockDet.det_blocks _ _ _ 0 (r_le_V i) _).1 (tri PP (Or.inr h)), map_mul]

theorem omega_lifts_vP : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.thP_ωP → R.thP_vP → ∀ i t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t :=
  fun _ hL _ hω hv i t _ _ _ hκ hκ' => om_lifts hL i t (hω i t) (hv i t) hκ hκ'

end GlobalTheory.VecInv
end

