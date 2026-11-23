module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafTW1OfAllConjugatesGood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2824
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

@[expose] public section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

open GlobalTheory.FlatVecSum (princ princ_good)

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · rw [show (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) by ring]
    exact hn1.mul hm1
  · rw [show (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) by rw [mul_inv]; ring]
    exact hn2.mul hm2

theorem exists_uniformiser (E : Type) [Field E] [NumberField E] (Q : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ ϖ : 𝓞 E, ϖ ≠ 0 ∧ ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2 := by
  have hx : ∀ PP : HeightOneSpectrum (𝓞 E), ∃ x ∈ PP.asIdeal, x ∉ PP.asIdeal ^ 2 := fun PP => by
    simpa using Ideal.exists_mem_pow_notMem_pow_succ PP.asIdeal PP.ne_bot PP.isPrime.ne_top 1
  choose x hx1 hx2 using hx
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Q)
    (fun PP => PP.asIdeal) (fun _ => 2) (fun PP _ => Ideal.prime_of_isPrime PP.ne_bot PP.isPrime)
    (fun PP _ PP' _ h e => h (HeightOneSpectrum.ext e)) (fun PP => x PP.1)
  have key : ∀ PP ∈ Q, y ∈ PP.asIdeal ∧ y ∉ PP.asIdeal ^ 2 := fun PP hPP => by
    have h1 := hy PP hPP
    have hle : PP.asIdeal ^ 2 ≤ PP.asIdeal := Ideal.pow_le_self (by norm_num)
    refine ⟨?_, fun h => hx2 PP ?_⟩
    · simpa using PP.asIdeal.add_mem (hle h1) (hx1 PP)
    · simpa using (PP.asIdeal ^ 2).sub_mem h h1
  by_cases hQ : Q.Nonempty
  · obtain ⟨PP, hPP⟩ := hQ
    exact ⟨y, fun h0 => (key PP hPP).2 (h0 ▸ Ideal.zero_mem _), key⟩
  · exact ⟨1, one_ne_zero, fun PP hPP => absurd ⟨PP, hPP⟩ hQ⟩

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle}
  {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ}

theorem isWeil_of_kerDat (hBo : BaseOf R i B) (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hχ : ChrEq B.de.chi ξ) : B.IsWeil 1 ω := by
  obtain rfl : χ = B.de.chi := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 _ _ _ hK.chr hχ
  rw [Base.IsWeil, mul_one, Base.mu, hBo.ψ, hBo.mu0, hBo.eta]
  exact hK.weil

theorem exists_om_eq (hC : GlobalTheory.Hk3.Core R F) (hG : QGuard R) (hV : VStd D i) (hB : B.Good) (hBo : BaseOf R i B)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hχ : ChrEq B.de.chi ξ) (hQ : ∃ t, B.de.Q ⊆ R.Q t) {N : ℕ} (hN : N ≠ 0)
    (hNQ : ∀ PP ∈ B.de.Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ∃ (z : GA D (Vc D i)) (c : ℂ), IsCentAt i B.de.Q z ∧ UnitOff N c ∧ ω (z, 1) φ = c • (princ B).vecBase := by
  obtain ⟨eg, eQ, fg, heg, heQ, hfg, hf⟩ := _root_.GlobalTheory.BaseCmp.flatTwoStep_holds D G Pl0 T0 A Ks R F hC i ξ χ ξR ω φ B hB hBo hK hχ
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_uniformiser D.host.E B.de.Q
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, hz, hzm⟩ := GlobalTheory.CentScal.exists_isCentAt_scalar D i B.de.Q eQ heQ (ϖ : D.host.E) hϖE
  obtain ⟨κ, hκ, hact⟩ := _root_.GlobalTheory.BaseCmp.dilKer_of_ne_zero D G Pl0 T0 A Ks R F hC hG i hV ξ χ ξR _ ω φ hK hQ N hN hNQ eg eQ fg heg heQ hfg ϖ
    (by first | exact hϖ0 | exact hϖE) hϖ z hzm
  obtain ⟨Gc, hGc, hSB, hvP⟩ := _root_.GlobalTheory.BaseCmp.liftKer_of_ne D G Pl0 T0 A Ks R F hC hG i hV ξ χ ξR _ ω φ hK hQ N hN hNQ eg eQ fg heg heQ hfg ϖ hϖ0 hϖ
  obtain ⟨Tm, hTm⟩ := hf.1
  refine ⟨z, κ * Gc, hz, unitOff_mul hκ hGc, ?_⟩
  have hcomp : ∀ x : WO (Vc D i) (Wc D i), dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ x) = x := by
    intro x
    ext a b
    simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  have e : (fun x => Gc * flatDat R i B.de.Q ξR eQ (dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ x))) =
      Gc • flatDat R i B.de.Q ξR eQ := funext fun x => by rw [hcomp]; rfl
  rw [hvP Tm hTm, hact Tm hTm _ hSB, hf.2 Tm hTm, mul_smul, e, map_smul]

theorem exists_trace_eq (hC : GlobalTheory.Hk3.Core R F) (hG : QGuard R) (hV : VStd D i) (hB : B.Good) (hBo : BaseOf R i B)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hχ : ChrEq B.de.chi ξ) (hQ : ∃ t, B.de.Q ⊆ R.Q t) {N : ℕ} (hN : N ≠ 0)
    (hNQ : ∀ PP ∈ B.de.Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ)
    (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (he : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c))
    (hU : ∀ g, e g ∈ B.G.P.H ↔ g ∈ U)
    (hψ : ∀ (u : U) (hu : e u ∈ B.G.P.H), ((B.G.P.chi ⟨e u, hu⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ u : D.what₂.LLˣ) : D.what₂.LL))
    {ω' : WeilRep D i} (hω' : B.IsWeil 1 ω') :
    ∃ k ∈ GfC (Vc D i), ∃ (c : ℂ) (m : ℕ), UnitOff N c ∧ ∀ h w, InCoefLat R i h w → InCoefLat R i (h * k) (((N : ℂ) ^ m) • w) ∧
      ∀ u, levelTrace R i U ψ (singleSeries R i ω φ h w u) =
        c • B.theta ω' (h * k) (R.ioP i (PiTensorProduct.tprod ℂ u) w) := by
  obtain ⟨z, c, ⟨-, hzf, a, ha, hs⟩, hc, hz⟩ := exists_om_eq hC hG hV hB hBo hK hχ hQ hN hNQ
  have hω := isWeil_of_kerDat hBo hK hχ
  have hW : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) _ _ ω := hω
  obtain ⟨m, hm⟩ := GlobalTheory.FreeBlockTwist.inCoefLat_pow R i (hC.lev.βV i) (GlobalTheory.SplitLinear.suppAt_inv hs) (p := N) fun PP hPP => by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), (GlobalTheory.FreeBlockTwist.cpt_sum ha PP).2 fun h => hPP (hNQ PP h), zero_add,
      GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((GlobalTheory.FreeBlockTwist.cpt_sum ha _).2 fun h =>
      hPP ((GlobalTheory.StdFrames.natCast_mem_cP PP N).1 (hNQ _ h)))
  refine ⟨z⁻¹, inv_mem hzf, c, m, hc, fun h w hw => ⟨hm m le_rfl h w hw, fun u => ?_⟩⟩
  have hfθ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (princ B).vecBase :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
      (Base.isThetaAt_vecAt (princ_good hB) (Base.admissible_empty_of_good (princ_good hB)) _) hB.frame.vac.2.theta
  have hφ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) φ := by
    obtain ⟨⟨h1, h0⟩, e, -, h⟩ := hK.vec
    rw [hBo.ψ]
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt h1 hC.models.inf h h0.theta
  set P := R.ioP i (PiTensorProduct.tprod ℂ u) w with hP
  have e1 : singleSeries R i ω φ h w u = c • (princ B).theta ω (h * z⁻¹) P := by
    funext g
    have e2 : singleSeries R i ω φ h w u g = ω (h, g) (B.F.fock φ P) 0 := by
      rw [hBo.fock_eq]
      rfl
    have e3 : ((h, g) : GA D (Vc D i) × GA D (Wc D i)) = (h * z⁻¹, g) * (z, 1) :=
      Prod.ext (inv_mul_cancel_right h z).symm (mul_one g).symm
    rw [e2, e3, map_mul, Module.End.mul_apply, Frame.fock,
      GlobalTheory.OrientedHeis.om_fin_pureTensorO B.F.ψ _ _ _ _ ω hW B.F.θ hB.frame.vac.2.inf z hzf 1 (one_mem _) _ _ _ _ φ P hφ, hz,
      Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, map_smul]
    rfl
  rw [e1, map_smul, _root_.GlobalTheory.TraceLevelPf.traceLevel D G Pl0 T0 A Ks R F hC i B hB hBo U ψ e he hU hψ ω hω]
  congr 1
  funext g
  exact congrFun (GlobalTheory.WeilUniq.weilDatum_unique D _ hB.frame.vac.1 _ _ _ _ ω ω' hω hω' _ _
    (Base.isThetaFunO_fock_vecAt hB (Base.admissible_empty_of_good hB) _ P)) 0

end Real

section Coef

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}

theorem mem_span_coefLat (hC : GlobalTheory.Hk3.Core R F) (hBo : BaseOf R i B)
    {c0L : ∀ j : Fin D.R.m, VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} (hc0 : IsCoefMap R c0L)
    (Φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (hval : ∀ w, Φ w ∈ B.valSpace) {c : ℂ} (hc : c ≠ 0)
    (hsc : ∀ y : VV D.what₂.LL (lamV D i), harmFn (Wc D i).rank B.w B.F.BS (Φ (c0L i y)) =
      c • coefFn D.what₂.embLL (lamV D i) (y : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D i).rank))
    (O O' : Subring ℂ) (hO' : ∀ a : 𝓞 D.what₂.LL, D.what₂.embLL a ∈ O') {h : GA D (Vc D i)} {w : (R.cV i).W}
    (hw : InCoefLat R i h w) : c⁻¹ • Φ w ∈ Submodule.span O'
      (B.coefLat (Formalism.L2.Host.embLL0 D) (labLL0 D) O (finPt _ h) : Set (PolF D (Wc D i).rank (Vc D i).rank)) := by
  obtain ⟨P, hP, rfl⟩ := _root_.GlobalTheory.CoefIndepProof.coefIndep D G Pl0 T0 A Ks R F hC i c0L hc0 h w hw
  have hlat : B.latAt (finPt _ h) = Bridge.hLat (Vc D i) (fin (Vc D i) h) :=
    GlobalTheory.LatAtHLat.latAt_eq_hLat D _ _ B (hBo.ΛS ▸ GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i)) _
  have hP' := GlobalTheory.T.dualWeylLattice_baseChange_span_proof D.host.E D.LL0 D.what₂.LL D.what₂.Tau _ (algebraMap D.LL0 D.what₂.LL) (labLL0 D) (lamV D i) _
    (GlobalTheory.FreeBlockTwist.hLat_full (Vc D i) (fin (Vc D i) h)) hP
  clear hP hw
  induction hP' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, e⟩ := hy
    refine Submodule.subset_span ?_
    change _ ∈ harmLat _ _ O _ B.w B.F.BS (B.latAt _)
    rw [mem_harmLat, hBo.lam, hlat]
    refine ⟨Submodule.smul_mem _ _ (hval _), Submodule.subset_span ⟨x, hx, ?_⟩⟩
    rw [map_smul, hsc, inv_smul_smul₀ hc, e, ← Scale.coefFn_map, MvPolynomial.map_map, Scale.coefFn_map]
    rfl
  | zero => rw [map_zero, map_zero, smul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), smul_add]; exact add_mem h1 h2
  | smul a y _ h1 =>
    rw [← algebraMap_smul D.what₂.LL a y, map_smulₛₗ, map_smul, smul_comm]
    exact Submodule.smul_mem _ (⟨_, hO' a⟩ : O') h1

end Coef

section Move

variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)


include hρ in
theorem exists_move {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    ∃ (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j)) (T : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank)
      (ζ : ℂ), (∃ n : ℕ, n ≠ 0 ∧ ζ ^ n = 1) ∧ (∀ P, ρ.theta i j b h P = ζ • ρ.theta i j b h' (T P)) ∧
      ∀ P ∈ ρ.lat i j b (ρ.eO i b).range h, ρ.IsDatum i j b s h' (T P) := by
  obtain ⟨hg, ha, -⟩ := _root_.GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hB := hρ.base i j b
  obtain ⟨γ, s, h', k, hs, hoff, hh', hsupp, e⟩ := _root_.GlobalTheory.RankReps.exists_rep_split_levJ D ρ hρ i j b h hh
  obtain ⟨n, hn, hk⟩ := _root_.GlobalTheory.BaseCmp.levLamRoot D _ _ (ρ.B i j b) _ k
  refine ⟨s, h', (ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j)), _, ⟨n, hn, by rw [inv_pow, hk, inv_one]⟩, fun P => ?_,
    fun P hP => ⟨hs, hoff, hh', hsupp, ?_⟩⟩
  · rw [← GlobalTheory.BaseClassSum.series_triv, GlobalTheory.BaseClassSum.series_move hB (D.sp.V_sig _) hg ha (hρ.weil i j b _ hg) hh hh' γ k e,
      GlobalTheory.BaseClassSum.series_triv]
  · have h1 := Base.act_mem_coefLat hB.frame (hρ.isCoefRing i b) γ⁻¹ (finPt _ h) (k⁻¹ : (ρ.B i j b).levJ (ρ.tw i b 0 ∅ 1))
      (Base.mem_St_of_mem_levJ (k⁻¹).2) hP
    rwa [e, map_inv, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left] at h1

end Move

section Read

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {X : Type} (rd : M →ₛₗ[eK] (X → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))


open GlobalTheory.BigOn.Exp in
theorem exists_scalar_of_readExt
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c))
    {x t : L ⊗[O] M} {ζ : ℂ} (h : readExt rd eL hL x = ζ • readExt rd eL hL t) : x = 0 ∨ ∃ a : L, eL a = ζ ∧ x = a • t := by
  classical
  let v := Module.finBasis (FractionRing O) M
  have key : ∀ x : L ⊗[O] M, ∃ c : _ → L, x = ∑ a, c a ⊗ₜ v a := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
    | tmul a f =>
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
      choose y hy using hd
      have hd0 : algebraMap O L d ≠ 0 := fun h0 => by
        have := hL d
        rw [h0, map_zero, eq_comm, map_eq_zero, IsFractionRing.to_map_eq_zero_iff] at this
        exact nonZeroDivisors.coe_ne_zero d this
      refine ⟨fun c => y c • ((algebraMap O L d)⁻¹ * a), ?_⟩
      have e : a ⊗ₜ[O] f = ((algebraMap O L d)⁻¹ * a) ⊗ₜ[O] ((d : O) • f) := by
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_inv_cancel_left₀ hd0]
      rw [e]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]
  obtain ⟨c, rfl⟩ := key x
  obtain ⟨d, rfl⟩ := key t
  have h1 : ∑ a, (eL (c a) - ζ * eL (d a)) • rd (v a) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, readExt_tmul, Finset.smul_sum, smul_smul] at h
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have h2 : ∀ a, eL (c a) = ζ * eL (d a) := fun a =>
    sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ h1 a)
  by_cases h0 : ∀ a, d a = 0
  · refine Or.inl (Finset.sum_eq_zero fun a _ => ?_)
    have : c a = 0 := eL.injective (by rw [h2, h0, map_zero, mul_zero])
    rw [this, TensorProduct.zero_tmul]
  · obtain ⟨a₀, ha₀⟩ := not_forall.1 h0
    have e : eL (c a₀ / d a₀) = ζ := by rw [map_div₀, h2, mul_div_cancel_right₀ _ ((map_ne_zero eL).2 ha₀)]
    refine Or.inr ⟨_, e, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    exact eL.injective (by rw [map_mul, e, h2])

end Read

theorem exists_of_integral {O K : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
    (e : K →+* ℂ) {N : ℕ} (hN : IsUnit (N : O)) {a : K} {n : ℕ} (h : IsIntegral ℤ ((N : ℂ) ^ n * e a)) :
    ∃ o : O, algebraMap O K o = a := by
  have h1 : IsIntegral ℤ ((N : K) ^ n * a) := by
    rw [← isIntegral_algHom_iff e.toIntAlgHom e.injective]
    simpa using h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h1.tower_top (A := O))
  obtain ⟨u, hu⟩ := hN.pow n
  refine ⟨(u⁻¹ : Oˣ) * y, ?_⟩
  rw [map_mul, hy, ← map_natCast (algebraMap O K), ← map_pow, ← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem isIntegral_of_root {ζ : ℂ} (h : ∃ n : ℕ, n ≠ 0 ∧ ζ ^ n = 1) : IsIntegral ℤ ζ :=
  let ⟨_, hn, e⟩ := h
  IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (e ▸ isIntegral_one)

end GlobalTheory.BaseCmp

namespace GlobalTheory.BigOn.Exp

open Formalism.MainNotions.DIV.Cons Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.BaseCmp

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}

theorem isUnit_ownAt (c : NChoice D) (w : D.what₂.places.Pl) : IsUnit ((ownAt D (D.plEq w) : ℕ) : c.Oe w) := by
  have hl : D.ntw.l (c.twI w) = Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := (c.twI_l w).trans (GlobalTheory.Mem.Top.Bl.resChar_eq_plc D w)
  have hco : (ownAt D (D.plEq w)).Coprime (D.ntw.l (c.twI w)) := by
    have hp := (D.ntw.lPrime (c.twI w)).out
    rw [ownAt, ← hl]
    split_ifs with h
    · rw [h]
      exact (Nat.coprime_primes D.host.pde'_prime D.host.pde_prime).2 D.host.pde_ne.symm
    · exact (Nat.coprime_primes D.host.pde_prime hp).2 (Ne.symm h)
  have h1 : IsUnit ((ownAt D (D.plEq w) : ℕ) : D.ntw.O (c.twI w)) := by
    by_contra h0
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hco
    have h2 := congrArg (Int.castRingHom (D.ntw.O (c.twI w))) hab
    simp only [map_add (f := _), map_mul, map_natCast, map_one] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2
      (h2 ▸ add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ (D.ntw.O_l _))))
  simpa using h1.map (algebraMap _ (c.Oe w))

theorem baseOf_of_realPin {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin p.R p.cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    BaseOf p.R.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hL := p.charW.base.lev
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b,
      lam := GlobalTheory.BaseLiftWeight.lam_eq D _ _ _ j _ hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b), delta := ?_, p := hP, q := hQ,
      c := funext fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ }
  rw [← liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

end GlobalTheory.BigOn.Exp

end
