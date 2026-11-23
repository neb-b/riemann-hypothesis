module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralMulRightN
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormalFramePeriod

variable {D : D7}

theorem setIntegral_mul_right_N {ρ : ℕ} (B : BesLev D ρ) (G : flagN B.d → ℂ)
    (hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n, G (γ * n) = G n) (y : flagN B.d) :
    ∫ n in B.vN.𝓝, G (n * y) ∂B.vN.ν = ∫ n in B.vN.𝓝, G n ∂B.vN.ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  haveI : DiscreteTopology (NFlagQ B.V B.d.e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B.V B.d.e => (⟨γ.1.1, γ.2⟩ : GQ B.V)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B.V => (x : GA D B.V)) hab))
  obtain ⟨K, hK, hcov⟩ := (_root_.GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (isIsoSub_e B.d)).1
  have hcov' : ∀ x : flagN B.d, ∃ s ∈ NFlagQ B.V B.d.e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : flagN B.d, B.vN.ν.map (· * a) = B.vN.ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice B.vN.ν (NFlagQ B.V B.d.e) hK hcov' a
  have hmp : MeasurePreserving (· * y) B.vN.ν B.vN.ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) B.vN.ν B.vN.ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) G B.vN.𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B.V B.d.e) ((· * y⁻¹) ⁻¹' B.vN.𝓝) B.vN.ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

theorem inner_N {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) (h : GA D B.A) :
    ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n ∂B.vN.ν =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
  obtain ⟨-, -, hconj, -, -⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨-, hψrat, hψconj, -⟩ := GlobalTheory.MixPer.charLaws D ψ hψ B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  have hx' : GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹ ∈ flagN B.d := hconj x hx h
  have hpy : psiBes ψ B.d 1 (vecB B.o B.ζ) (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x := hψconj x h
  have hn1 : psiBes ψ B.d 1 (vecB B.o B.ζ) x * star (psiBes ψ B.d 1 (vecB B.o B.ζ) x) = 1 := by
    have hnorm : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) x‖ = 1 := by simp only [psiBes, psiE]; exact hψ.2.1 _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ * n) = besFun ψ 1 B.d B.o B.ζ φ f h n := fun γ' hγ' n => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 n.2, hψrat _ _ hγ'Q, one_mul, mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  let y : flagN B.d := ⟨_, hx'⟩
  have hpt : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * besFun ψ 1 B.d B.o B.ζ φ f h (n * y) := fun n => by
    simp only [besFun, rTrans, Subgroup.coe_mul, y]
    rw [psiBes_mul B.d ψ 1 _ n.2 hx', hpy, star_mul]
    have e1 : (n : GA D B.V) * (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) *
        GlobalTheory.MixPer.embA B.d B.o h = (n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x := by group
    rw [e1]
    linear_combination (-(φ h * f ((n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x) *
      star (psiBes ψ B.d 1 (vecB B.o B.ζ) (n : GA D B.V)))) * hn1
  simp_rw [hpt]
  rw [integral_const_mul, setIntegral_mul_right_N B _ hG y]

theorem per_flagN {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) :
    B.per ψ φ (rTrans x f) = psiBes ψ B.d 1 (vecB B.o B.ζ) x * B.per ψ φ f := by
  unfold BesLev.per besPer
  simp_rw [inner_N B ψ hψ.1 φ f hf hx]
  exact integral_const_mul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_embA (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) {g : GL n k}
    {h : GA D B.A} (hh : p.IsLoc FA h g) : p.IsLoc F (GlobalTheory.MixPer.embA B.d B.o h) (embX c g) := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  rw [GlobalTheory.MixPer.embA_apply]
  refine ⟨GlobalTheory.LocGrp.suppAt_wittLeviEmbedding B.d (GlobalTheory.LocGrp.suppAt_emb B.o hh.1),
    GlobalTheory.LocGrp.eq_embX F _ g ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (GlobalTheory.LocGrp.intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r =>
      (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩
      (hY _ j (by simp only; omega))

end GlobalTheory.NormalFramePeriod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelSectionWeylElementEqSchrodingerIntegral
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.WeylValue

variable {D : D7}

theorem integral_periodise {m n : ℕ} {ν : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hν : IsCovolOne (ratMx D m n) ν 𝓨) (φ F : Mx D m n → ℂ) (hφ : Integrable φ ν)
    (hF : ∀ x, HasSum (fun ξ : Matrix (Fin m) (Fin n) D.host.E => φ (x + rat ξ)) (F x)) :
    ∫ x in 𝓨, F x ∂ν = ∫ x, φ x ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hν.1
  let e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
    Equiv.ofBijective (fun ξ => ⟨rat ξ, rat_mem ξ⟩)
      ⟨fun a b h => rat_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨ξ, hξ⟩ := mem_ratMx.1 g.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩
  have h1 : ∀ x, F x = ∑' g : ratMx D m n, φ (g +ᵥ x) := fun x => by
    rw [← (hF x).tsum_eq, ← e.tsum_eq]
    refine tsum_congr fun ξ => ?_
    show φ (x + rat ξ) = φ (rat ξ + x)
    rw [add_comm]
  simp only [h1]
  rw [hν.2.1.integral_eq_tsum'' φ hφ]
  refine integral_tsum (fun g => ?_) ?_
  · exact ((hφ.comp_add_left (g : Mx D m n)).aestronglyMeasurable).restrict
  · rw [← hν.2.1.lintegral_eq_tsum'' fun x => ‖φ x‖ₑ]
    exact hφ.2.ne

theorem pY_weyl (A : HSp D) {w : GA D (dblSp A)} (hw : IsWeyl A w) :
    ((dblDec A).pY ⬝ mt (dblSp A) w : Mx D A.rank (dblSp A).rank) = lowC A w ⬝ (dblDec A).pX := by
  have h0 : ((dblDec A).j0 ⬝ (dblDec A).p0 : Mx D (dblSp A).rank (dblSp A).rank) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  have h1 := (dblDec A).sum_eq_one
  rw [h0, add_zero] at h1
  have h2 := hw.2
  rw [← Matrix.mul_assoc] at h2
  rw [← Matrix.mul_one ((dblDec A).pY ⬝ mt (dblSp A) w), ← h1, Matrix.mul_add, ← Matrix.mul_assoc _ (dblDec A).jY, h2,
    Matrix.zero_mul, add_zero, lowC]
  simp only [Matrix.mul_assoc]

theorem swSec_weyl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ w, IsWeyl A w → swSec A B omh ν 𝓨 f w = ∫ x, sch ψ A B ν 𝓨 f x ∂ν := by
  intro D ψ A B χB omh hω ν 𝓨 hν f hf w hw
  have hp := pY_weyl A hw
  have hm : lowC A w ∈ ratMx D A.rank A.rank :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff _ _).1 hw.1) (rat_mem _))
  let n : Mx D A.rank A.rank := (dblDec A).pX ⬝ (mt (dblSp A) w⁻¹ ⬝ (dblDec A).jY)
  have hn : n ∈ ratMx D A.rank A.rank :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff _ _).1 (inv_mem hw.1)) (rat_mem _))
  have hmn : lowC A w * n = 1 := by
    show lowC A w ⬝ ((dblDec A).pX ⬝ (mt (dblSp A) w⁻¹ ⬝ (dblDec A).jY)) = 1
    rw [← Matrix.mul_assoc, ← hp, Matrix.mul_assoc, ← Matrix.mul_assoc (mt (dblSp A) w), mt_mul_inv, Matrix.one_mul,
      HypDec.pY_jY]
  have h1 : ∀ z : WO A B, omh (w, 1) f (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B z) = f ((dblDec A).extX B (z ⬝ lowC A w)) := fun z => by
    rw [GlobalTheory.RatSubst.om_rat_left_apply D ψ _ _ _ _ omh hω f hf w hw.1, actO_eq, inv_inv, mt_one, Matrix.one_mul,
      ← extY_dblDec, HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, hp, Matrix.mul_assoc]
  have hper : ∀ γ ∈ ratMx D B.rank A.rank, ∀ a, f ((dblDec A).extX B (γ + a)) = f ((dblDec A).extX B a) := by
    intro γ hγ a
    obtain ⟨δ, hδ⟩ : (dblDec A).extX B γ ∈ ratMx D _ _ := ratMx_mul hγ (rat_mem _)
    have h := hf.quasi δ ((dblDec A).extX B a)
    rw [show ratW B (dblSp A) δ = (dblDec A).extX B γ from hδ, HypDec.symplOH_extX_extX, neg_zero,
      AddChar.map_zero_eq_one, one_mul] at h
    rw [map_add (f := _), h]
  unfold swSec GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero
  simp only [h1]
  have hchange : ∫ a in 𝓨, f ((dblDec A).extX B (a * lowC A w)) ∂ν =
      ∫ a in 𝓨, f ((dblDec A).extX B a) ∂ν := by
    obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D B.rank A.rank
    let e : Mx D B.rank A.rank ≃+ Mx D B.rank A.rank :=
      { toFun := fun a => a * lowC A w
        invFun := fun a => a * n
        left_inv := fun a => by simp only [Matrix.mul_assoc, hmn, Matrix.mul_one]
        right_inv := fun a => by simp only [Matrix.mul_assoc, mul_eq_one_comm.1 hmn, Matrix.mul_one]
        map_add' := fun a b => Matrix.add_mul _ _ _ }
    have he : Continuous e := continuous_id.matrix_mul continuous_const
    have he' : Continuous e.symm := continuous_id.matrix_mul continuous_const
    have hr : ∀ x, e x ∈ ratMx D B.rank A.rank ↔ x ∈ ratMx D B.rank A.rank := fun x =>
      ⟨fun h => by
        have h2 := ratMx_mul h hn
        have h3 : e x * n = x := e.symm_apply_apply x
        rwa [h3] at h2,
       fun h => ratMx_mul h hm⟩
    obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hν e he he' hr
    rw [← covolOne_integral_eq hν h1 (fun a => f ((dblDec A).extX B a)) hper,
      hemb.setIntegral_map, Set.preimage_image_eq _ e.injective]
    rfl
  refine hchange.trans ?_
  exact integral_periodise hν _ _ (_root_.GlobalTheory.Core.Rk.SchInt.sch_continuous_integrable D ψ hω.std A B ν 𝓨 hν f hf).2
    fun x => (_root_.GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch D ψ hω.std A B ν 𝓨 hν f hf x).2

end GlobalTheory.Core.Rk.WeylValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocMod.GValProof

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_frame {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) : Fintype.card Y = N := by
  apply le_antisymm
  · calc Fintype.card Y = (F.γ * F.β).rank := by rw [F.γβ, Matrix.rank_one]
      _ ≤ F.β.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin N) := Matrix.rank_le_card_height _
      _ = N := Fintype.card_fin N
  · calc N = Fintype.card (Fin N) := (Fintype.card_fin N).symm
      _ = (F.β * F.γ).rank := by rw [F.βγ, Matrix.rank_one]
      _ ≤ F.γ.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card Y := Matrix.rank_le_card_height _

theorem core_of_bes (p : Place D k) {ρ : ℕ} (B : BesLev D ρ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (G : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA G) :
    ∃ F₀ : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F₀ := by
  obtain ⟨hc, hA, -, hz, -⟩ := h
  let f : D.host.E →+* k := p.π.comp (incA D)
  have hpr : ∀ a, p.pr a = f a := fun _ => rfl
  let e : n ⊕ Unit → n ⊕ Fin c := Sum.elim Sum.inl fun _ => Sum.inr ⟨ρ, by omega⟩
  have he : Function.Injective e := by
    rintro (a | ⟨⟩) (b | ⟨⟩) hab <;> simp_all [e]
  let βA : Matrix (Fin B.V₀.rank) n k := B.o.iA.map p.pr * FA.β
  let β : Matrix (Fin B.V₀.rank) (n ⊕ Unit) k :=
    Matrix.of fun r y => Sum.elim (fun a => βA r a) (fun _ => s * p.pr (vecB B.o B.ζ r)) y
  let I : Matrix (Fin B.V.rank) (Fin B.V₀.rank) k := B.d.i₀.map p.pr
  have hmap : I * B.o.iA.map p.pr = (B.d.i₀ * B.o.iA).map p.pr := (Matrix.map_mul (f := f)).symm
  have hIβ : I * β = G.β.submatrix id e := by
    ext r (a | ⟨⟩)
    · simp only [submatrix_apply, id, e, Sum.elim_inl]
      rw [hA]
      have : (I * β) r (Sum.inl a) = (I * βA) r a := by
        simp only [Matrix.mul_apply, β, Matrix.of_apply, Sum.elim_inl]
      rw [this, ← Matrix.mul_assoc, hmap]
    · simp only [submatrix_apply, id, e, Sum.elim_inr]
      rw [hz ⟨ρ, by omega⟩ rfl r, hpr, RingHom.map_mulVec]
      simp only [Matrix.mul_apply, β, Matrix.of_apply, Sum.elim_inr, mulVec, dotProduct, Finset.mul_sum, I,
        Function.comp_apply, hpr]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.map_apply, hpr]
      ring
  let γ : Matrix (n ⊕ Unit) (Fin B.V₀.rank) k := G.γ.submatrix e id * I
  have hγβ : γ * β = 1 := by
    rw [Matrix.mul_assoc, hIβ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, G.γβ, Matrix.submatrix_one _ he]
  have hcard : Fintype.card (n ⊕ Unit) = B.V₀.rank := by
    have h1 := card_frame G
    have h2 := B.d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1 ⊢
    omega
  have hβγ : β * γ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hcard)).1 hγβ
  exact ⟨⟨β, γ, hβγ, hγβ⟩, fun r a => rfl, fun r => rfl⟩

theorem hz_link (p : Place D k) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) :
    p.hz B = -p.xi ^ 2 * p.hz B' := by
  let f : D.host.E →+* k := p.π.comp (incA D)
  have hpr : ∀ a, p.pr a = f a := fun _ => rfl
  rw [Place.hz, Place.hz, Place.xi, l.norm, hpr, hpr, hpr, map_mul, map_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]
  ring

theorem cont_of_cond (ψ : AddChar k Circle) (h : HasConductor ψ 1) : Continuous ψ := h.continuous

theorem one_mem_SB (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] :
    (Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => (1 : ℂ)) ∈ SB (Matrix n n' k) := by
  set S : Set (Matrix n n' k) := {x | ∀ r q, x r q ∈ 𝒪[k]} with hSdef
  have hS : (S : Set (n → n' → k)) = Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h r _ q _ => h r q, fun h r q => h r (Set.mem_univ _) q (Set.mem_univ _)⟩
  have hO : IsOpen S := by
    change IsOpen (S : Set (n → n' → k))
    rw [hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      Valuation.isOpen_integer (v := valuation k)
  have hK : IsCompact S := by
    change IsCompact (S : Set (n → n' → k))
    rw [hS]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => by simp [Set.indicator, hx]⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ S
  · exact ⟨S, hO, hx, fun y hy => by simp [Set.indicator, hy, hx]⟩
  · exact ⟨Sᶜ, hK.isClosed.isOpen_compl, hx, fun y hy => by
      have hy' : y ∉ S := hy
      simp [Set.indicator, hy', hx]⟩

theorem sliceCol_mem {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {f : Matrix n (n' ⊕ Unit) k → ℂ}
    (hf : f ∈ SB _) : (fun a : Matrix n n' k => f (fromCols a 0)) ∈ SB _ := by
  have hc : Continuous fun a : Matrix n n' k => fromCols a (0 : Matrix n Unit k) := by
    refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · simp only [fromCols_apply_inl]; exact continuous_id.matrix_elem i j
    · simp only [fromCols_apply_inr]; exact continuous_const
  have hd : Continuous fun x : Matrix n (n' ⊕ Unit) k => x.toCols₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)
  refine ⟨hf.1.comp_continuous hc, HasCompactSupport.intro (hf.2.isCompact.image hd) fun a ha => ?_⟩
  by_contra h0
  exact ha ⟨fromCols a 0, subset_tsupport _ h0, toCols₁_fromCols _ _⟩

theorem sliceRow_mem {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {f : Matrix (n ⊕ Unit) n' k → ℂ}
    (hf : f ∈ SB _) : (fun a : Matrix n n' k => f (fromRows a 0)) ∈ SB _ := by
  have hc : Continuous fun a : Matrix n n' k => fromRows a (0 : Matrix Unit n' k) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · simp only [fromRows_apply_inl]; exact continuous_id.matrix_elem i j
    · simp only [fromRows_apply_inr]; exact continuous_const
  have hd : Continuous fun x : Matrix (n ⊕ Unit) n' k => x.toRows₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem (Sum.inl i) j
  refine ⟨hf.1.comp_continuous hc, HasCompactSupport.intro (hf.2.isCompact.image hd) fun a ha => ?_⟩
  by_contra h0
  exact ha ⟨fromRows a 0, subset_tsupport _ h0, toRows₁_fromRows _ _⟩
end

theorem gval : ∀ (D : D7), FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (c₁ : WO B.A J.W₀ →₀ ℂ) (c₂ : WO J.W₀ B'.A →₀ ℂ),
    p.IsCombAt ψ F.F₀ F.F₁ c₁ ((S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1) →
    p.IsCombAt ψ F.F₁ F.F₂ c₂ ((S.T t).entry S.ψ ν (j + 1) c H 1 1) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂,
    Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) → Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) → IsOne O₁ → IsOne O₂ →
    GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (T₂ Φ₂)) =
      C • biComb ψ B.A J.W₀ B'.A c₁ c₂ (GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ O₁)) (flatFB s₂ (T₂ O₂))) := by
  intro D hBF hFB hCL hSym k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hstd hchar j c H
  by_cases hc : ∃ r, c = 2 * r
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro σ B J B' F
    exact absurd ⟨σ, by have := F.bes.1; omega⟩ hc
  obtain ⟨r, hr⟩ := hc
  obtain ⟨-, hPC, hPR, hDS⟩ := hSym k ν hν s κ S t
  obtain ⟨-, C, hC, hval⟩ := hDS j c H r hr
  refine ⟨(C : ℂ), by exact_mod_cast hC.ne', ?_⟩
  intro σ B J B' F s₁ s₂ l vL c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hΦ₁ hΦ₂ hO₁ hO₂
  have hσ : σ = r := by have := F.bes.1; omega
  subst hσ
  have hψc : Continuous S.ψ := cont_of_cond S.ψ S.cond
  obtain ⟨C₀, hC₀⟩ := core_of_bes p B F.s F.F₀ F.G₀ F.bes
  obtain ⟨C₂, hC₂⟩ := core_of_bes p B' (F.s * p.xi) F.F₂ F.G₂ F.bes'
  have hjac : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := by
    rw [← hz_link p B B' l]; exact F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF k p ν hν.1 ψ S.ψ hchar (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁ hC₀ F.bes F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB k p ν hν.1 ψ S.ψ hchar σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂ hjac hC₂ F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL k p ν hν.1 ψ hstd S.ψ hchar (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hfl := GlobalTheory.LocFlat.flat_SB_onto k S.ψ ν hψc hν.1
  have m₁ := fun Φ : SB _ => ((hfl (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 Φ.1 Φ.2
  have m₂ := fun Φ : SB _ => ((hfl (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) (c + 1) (σ + 1) (by omega)).2 (by omega)).1 Φ.1 Φ.2
  let Ψ₁ : SB _ := ⟨_, m₁ Φ₁⟩
  let Ψ₂ : SB _ := ⟨_, m₂ Φ₂⟩
  let P₁ : SB _ := ⟨_, m₁ O₁⟩
  let P₂ : SB _ := ⟨_, m₂ O₂⟩
  rw [hU₁e Φ₁ Ψ₁ rfl, hU₂e Φ₂ Ψ₂ rfl, hU₁e O₁ P₁ rfl, hU₂e O₂ P₂ rfl]
  obtain ⟨Ξ, hΞ, e1⟩ := hΛe Ψ₁ Ψ₂
  obtain ⟨ΞO, hΞO, e2⟩ := hΛe P₁ P₂
  rw [e1, e2]

  have hE₁ : (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 ∈ SB _ := by
    obtain ⟨C', hC', hpc⟩ := hPC j (c + 1) (by omega) (σ + 1) (by omega)
    have hs := sliceCol_mem Ψ₁.2
    have e : (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 = (C'⁻¹ : ℂ) • fun a => Ψ₁.1 (fromCols a 0) := by
      funext a
      simp only [Ψ₁, Pi.smul_apply, smul_eq_mul]
      rw [hΦ₁, hpc]
      have hC'0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'.ne'
      simp only [toCols₁_fromCols, fromCols_apply_inr, Matrix.zero_apply]
      have hz : (fun _ => (0 : k)) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (σ + 1))⁻¹ := (box _ _).zero_mem
      simp only [hz, if_true, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ hC'0, one_mul]
    rw [e]; exact (SB _).smul_mem _ hs
  have hE₂ : (S.T t).entry S.ψ ν (j + 1) c H 1 1 ∈ SB _ := by
    obtain ⟨C', hC', hpr⟩ := hPR (j + 1) c H σ hr
    have hs := sliceRow_mem Ψ₂.2
    have e : (S.T t).entry S.ψ ν (j + 1) c H 1 1 = (C'⁻¹ : ℂ) • fun a => Ψ₂.1 (fromRows a 0) := by
      funext a
      simp only [Ψ₂, Pi.smul_apply, smul_eq_mul]
      rw [hΦ₂, hpr]
      have hC'0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'.ne'
      simp only [toRows₁_fromRows, fromRows_apply_inr, Matrix.zero_apply]
      have hz : a.fromRows (0 : Matrix Unit (XIx (Fin κ) t (j + 1)) k) (Sum.inr ()) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (σ + 1)) := (box _ _).zero_mem
      simp only [hz, if_true, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ hC'0, one_mul]
    rw [e]; exact (SB _).smul_mem _ hs
  let E₁ : SB _ := ⟨_, hE₁⟩
  let E₂ : SB _ := ⟨_, hE₂⟩
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hΞ' : ∀ q, ((C : ℂ)⁻¹ • Ξ).1 q = E₁.1 q.1 * E₂.1 q.2 := by
    intro q
    rw [Submodule.coe_smul, Pi.smul_apply, hΞ]
    simp only [Ψ₁, Ψ₂, E₁, E₂]
    rw [hΦ₁, hΦ₂, hval q, smul_eq_mul]
    field_simp
  have hΞe : Ξ = (C : ℂ) • ((C : ℂ)⁻¹ • Ξ) := by rw [smul_smul, mul_inv_cancel₀ hCne, one_smul]

  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator k S.ψ ν S.cond hν
  let Q₁ : SB (Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k) := ⟨_, one_mem_SB _ _⟩
  let Q₂ : SB (Matrix (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) k) := ⟨_, one_mem_SB _ _⟩
  have hP₁ : P₁.1 = Set.indicator {x : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
    simp only [P₁]
    rw [hO₁, (hun (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (XIx (Fin κ) t j) (c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)]
  have hP₂ : P₂.1 = Set.indicator {x : Matrix (XIx (Fin κ) t (j + 1 + 1) ⊕ Unit) (XIx (Fin κ) t (j + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
    simp only [P₂]
    rw [hO₂, (hun (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1) (σ + 1)).2.1 (by omega) (by omega)]
  have hΞO' : ∀ q, ΞO.1 q = Q₁.1 q.1 * Q₂.1 q.2 := by
    intro q
    rw [hΞO, hP₁, hP₂]
    exact (hun (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1 + 1)) 0 0).2.2 q
  have hbi := (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ _ _ _).1 B.A J.W₀ B'.A F.F₀ F.F₁ F.F₂ Λ c₁ c₂ E₁ Q₁ E₂ Q₂ ((C : ℂ)⁻¹ • Ξ) ΞO hΛ hc₁ hc₂ rfl rfl hΞ' hΞO'
  rw [hΞe, map_smul, hbi]

theorem gval_of_laws : ∀ (D : D7), FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse → GVal D := by
  intro D hBF hFB hCL hSym k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hchar j c H
  by_cases hstd : IsStdChar D ψ (-1)
  · exact gval D hBF hFB hCL hSym k ν hν p s κ S t ψ hstd hchar j c H
  · refine ⟨1, one_ne_zero, ?_⟩
    intro σ B J B' F s₁
    exact absurd s₁.weil.std hstd

end GlobalTheory.LocMod.GValProof
end
end

