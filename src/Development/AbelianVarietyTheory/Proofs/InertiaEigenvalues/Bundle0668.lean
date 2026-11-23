module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorMulLocalOperatorHasSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0663
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0567
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerNeSpherical
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

theorem scalar_of_eigen {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (P : Submodule ℂ H)
    (Wop : H →L[ℂ] H) (hinj : Function.Injective Wop) (heig : ∀ y ∈ P, ∃ z : ℂ, Wop y = z • y) :
    ∃ l : ℂ, l ≠ 0 ∧ ∀ x ∈ P, Wop x = l • x := by
  by_cases h : ∃ x0 ∈ P, x0 ≠ 0
  · obtain ⟨x0, hx0, hne⟩ := h
    obtain ⟨l, hl⟩ := heig x0 hx0
    refine ⟨l, ?_, ?_⟩
    · rintro rfl
      apply hne
      apply hinj
      rw [hl, zero_smul, map_zero]
    · intro x hx
      obtain ⟨lx, hlx⟩ := heig x hx
      obtain ⟨m, hm⟩ := heig (x + x0) (P.add_mem hx hx0)
      rw [map_add (f := _), hlx, hl, smul_add] at hm
      by_cases hmx : m = lx
      · subst hmx
        have : (l - m) • x0 = 0 := by
          rw [sub_smul]; exact sub_eq_zero.2 (add_left_cancel hm)
        rcases smul_eq_zero.1 this with h1 | h1
        · rw [hlx, sub_eq_zero.1 h1]
        · exact absurd h1 hne
      · have hx' : x = ((l - m) / (m - lx)) • x0 := by
          have e1 : (m - lx) • x = (l - m) • x0 := by
            rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add]
            rw [← hm]; abel
          have hne' : m - lx ≠ 0 := sub_ne_zero.2 hmx
          rw [div_eq_mul_inv, mul_comm, mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hne', one_smul]
        rw [hx', map_smul, hl, smul_comm]
  · push_neg at h
    refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    rw [h x hx, map_zero, smul_zero]

set_option maxHeartbeats 4000000 in
theorem innerNe_main {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hL : Laws R F) (i : Fin D.R.m) (t : T) (hFS : FinSum R i t) (hFM : FinMult R i t) (hLF : LevFix R i t)
    (hVN : VecNe R i t) (hLS : LocSmall R i t) (hBS : BadSupp R i t) (hLP : LevProd R i) (hTL : TransLaws R i) :
    InnerNe R i t ∅ := by
  intro th hth c
  have hcov := @_root_.GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws D G _ _ Pl0 T A Ks _ _ _ R F hL i
  obtain ⟨μ, 𝓕, hμ⟩ := hcov
  have hleft := @_root_.GlobalTheory.RawLift.CoefLeft.coef_lev_mul D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF μ 𝓕 hμ
  have hfa := @GlobalTheory.T.hasSum_innerProduct_finsupp_localCosetFamilies D G _ _ Pl0 T A Ks _ _ _ R i t hLP hTL hFM hLF hVN hFS th hth μ 𝓕 hμ
  have hsm := @_root_.GlobalTheory.RawLift.Eu.acoef_small D G _ _ Pl0 T A Ks _ _ _ R i t hLS μ 𝓕 hμ
  obtain ⟨a, ha, hfam⟩ := hfa
  obtain ⟨s, hs, hs1, hsC⟩ := hsm
  have hconv := @_root_.GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum D G _ _ Pl0 T A Ks _ _ _ R i t hLS hTL hLF μ 𝓕 hμ hleft
  have hupd := @_root_.GlobalTheory.RawLift.Eu.bop_famProd_update D G _ _ Pl0 T A Ks _ _ _ R i hTL
  have heig := @GlobalTheory.T.localOperator_scalar_on_sphericalEigenspace D G _ _ Pl0 T A Ks _ _ _ R F hL i t hBS hLF hLS hLP hTL μ 𝓕 hμ hleft c
  have hUpd : ∀ v (f : ∀ v, Eu.LX R i v), {w | f w ≠ Eu.lx0 R i w}.Finite → f v = Eu.lx0 R i v →
      HasSum (fun x => Eu.acoef R i t μ 𝓕 v x • Eu.Bfam R i (Function.update f v x))
        (Eu.Bfam R i f * Eu.Zop R i t μ 𝓕 v) := by
    intro v f hf hv
    obtain ⟨hG, hB⟩ := hupd f hf v hv
    have := hconv v _ hG
    unfold Eu.Bfam
    simp only [hB]
    exact this
  have hEu := _root_.GlobalTheory.eulerOp_injective_eigen (HeightOneSpectrum (𝓞 D.host.F)) (Eu.LX R i) (Eu.lx0 R i)
    (R.HW i (sg0 D A)).H (Eu.acoef R i t μ 𝓕) s (Eu.Bfam R i) (Eu.Zop R i t μ 𝓕)
    (local_coefficient_trivial_level_coset hLF hVN hμ) hs hs1 hsC (fun f => bop_norm R i _)
    (by unfold Eu.Bfam; rw [localCosetFamilyRepresentativeProd_trivial_eq_one]; exact bop_one hTL) hUpd
  obtain ⟨Wop, hW, hinj, hWe⟩ := hEu
  have hip : ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = (a : ℂ) * ⟪x, Wop y⟫_ℂ := by
    intro x y
    let φ : ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H) →L[ℂ] ℂ :=
      (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ _ y)
    have h1 := (hW.mapL φ).mul_left (a : ℂ)
    have h2 := hfam x y
    refine h2.unique ?_
    simpa [φ, inner_smul_right] using h1
  have hE : ∀ y ∈ part R i ∅ c, ∃ z : ℂ, Wop y = z • y := by
    intro y hy
    have hz := fun v => heig y hy v
    choose z hz using hz
    exact ⟨_, hWe y z hz⟩
  have hsc := scalar_of_eigen (part R i ∅ c) Wop hinj hE
  obtain ⟨l, hl, hlx⟩ := hsc
  refine ⟨(a : ℂ) * (starRingEnd ℂ) l, mul_ne_zero (by exact_mod_cast ha.ne') (by simpa using hl), ?_⟩
  intro x hx y
  rw [← inner_conj_symm, hip y x, hlx x hx, inner_smul_right, map_mul, map_mul, Complex.conj_ofReal,
    inner_conj_symm]
  ring

end GlobalTheory.RawLift.Eu

namespace GlobalTheory.RawLift

theorem innerNe_spherical : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FinSum R i t → FinMult R i t → LevFix R i t → VecNe R i t → LocSmall R i t → BadSupp R i t → LevProd R i → TransLaws R i → InnerNe R i t ∅ :=
  fun _ _ _ _ _ _ _ _ _ _ _ R F hL _ i t hFS hFM hLF hVN hLS hBS hLP hTL =>
    Eu.innerNe_main R F hL i t hFS hFM hLF hVN hLS hBS hLP hTL

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotientStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_factor_of_spherical_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsSubquotient π (prodIrr x hd) → IsSpherical π → ∀ a, IsSpherical (x a).rep := by
  first | exact @GlobalTheory.LocLanglands.SphFac.isSpherical_factor | exact GlobalTheory.LocLanglands.SphFac.isSpherical_factor | (intros; apply GlobalTheory.LocLanglands.SphFac.isSpherical_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExtensionUniqueOnCuspidal
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LangExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  haveI : LeftCommutative (WD.lpSum (h := h)) :=
    ⟨fun a b c => by rw [← WD.lpSum_assoc, WD.lpSum_comm a b, WD.lpSum_assoc]⟩
  exact hp.foldr_eq _

theorem charZero_adicCompletion : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

end GlobalTheory.LocLanglands.LangExt


open GlobalTheory.LocLanglands.LangExt in
theorem GlobalTheory.LocLanglands.exists_isLExt : LanglandsExhaustionGL → LanglandsMultisegments → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (r : IrrGL (k := w.adicCompletion E) → WD h), (∃ rc, IsLExt r rc) ∧ ∀ rc, IsLExt r rc → ∀ x : IrrGL (k := w.adicCompletion E), x.IsCusp → rc x = r x := by
  intro hX hM E Ω _ _ _ _ _ A w h r
  haveI : CharZero (w.adicCompletion E) := LangExt.charZero_adicCompletion
  refine ⟨⟨fun x => segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList, ?_⟩, ?_⟩
  · intro l x hl
    have hm := Classical.choose_spec (hX (w.adicCompletion E) x)
    have he := (hM (w.adicCompletion E)).1 _ _ x hm hl
    show segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList = segSum r l
    unfold segSum
    apply LangExt.sumList_perm
    apply List.Perm.map
    apply Multiset.coe_eq_coe.1
    rw [Multiset.coe_toList]
    exact he
  · intro rc hrc x hx
    have h1 := hrc [.single x hx] x (single_spec hx).2.2.2
    rw [h1]
    change (((r x).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) 1)).lpSum (WD.lpZero (h := h)) = r x
    rw [WD.lpSum_zero]
    have h2 := (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (r x)).1
    have h3 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
    rw [h3]
    exact h2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSurjectionGoodCrystallineLattices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TheoremT


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem liftF_of_isGood : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → IsGood a ϖ Pl T₂ Sig U → g.LiftF (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig))) := by
  intro hBS hFon l _ a e _ _ ϖ LL _ _ Pl AI hStd N η H Sig U hNum T₁ T₂ g hg hG₁ hG₂
  have hN2 := hNum.two_le
  have hlarge := hNum.large
  have hHN : 4 * H ≤ H * N ^ 2 := by
    have h4 : 4 ≤ N ^ 2 := by nlinarith
    calc 4 * H = H * 4 := by ring
      _ ≤ H * N ^ 2 := Nat.mul_le_mul_left H h4
  have hl2 : l ≠ 2 := by intro h; subst h; nlinarith
  have h8 : 8 * H + 1 < l := by nlinarith
  obtain ⟨T₀, f, hSES, hG₀⟩ := GlobalTheory.T.isGoodLattice_kernel_of_surjection_goodLattice hFon l a e ϖ LL Pl AI hStd Sig U T₁ T₂ g hg hG₁
  obtain ⟨P₀, -⟩ := _root_.GlobalTheory.BKGal.exists_pack_isOfType hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₀ hG₀
  obtain ⟨P₁, hP₁⟩ := _root_.GlobalTheory.BKGal.exists_pack_isOfType hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₁ hG₁
  obtain ⟨P₂, hP₂⟩ := _root_.GlobalTheory.BKGal.exists_pack_isOfType hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₂ hG₂
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.BKGal.PackMap.main hBS l a e ϖ LL η H T₀ T₁ P₀ P₁ f
  obtain ⟨G, hG⟩ := _root_.GlobalTheory.BKGal.PackMap.main hBS l a e ϖ LL η H T₁ T₂ P₁ P₂ g
  have hEx := GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices l a e ϖ LL (Fin P₀.n) (Fin P₁.n) (Fin P₂.n) P₀.D.toPhiMod P₁.D.toPhiMod
    P₂.D.toPhiMod T₀ T₁ T₂ P₀.R.I P₁.R.I P₂.R.I f g F.toHom G.toHom hSES hF hG
  have hAdm : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.Admissible l e N η H Sig U :=
    ⟨hNum.frob_mem, hNum.zero_mem_Sig, hNum.card_Sig, hNum.two_le, hNum.range_U, hNum.zero_mem_U,
      hNum.card_U, hNum.one_le, hNum.lt, hNum.large⟩
  have hpot₂ := _root_.GlobalTheory.GalPot.potential_class l a e _ _ (thetaW a LL) ϖ (Fin P₂.n) η H P₂.D T₂ P₂.R
  unfold LatHom.LiftF
  intro c hc

  obtain ⟨y₂, hy₂, hMon₂, hCl₂⟩ :=
    _root_.GlobalTheory.BKGal.ExtClass.main hBS hFon l a e ϖ LL Pl AI hStd N η H Sig U hNum T₂ hG₂ P₂ c hc

  obtain ⟨y₂', hy₂', m₂, hm₂, hsum⟩ :=
    Submodule.mem_sup.1 ((_root_.GlobalTheory.divisible_of_BKDat _ _ l e a _ η H P₂.D).2 y₂ hy₂)
  have hrew : y₂' + P₂.D.phi m₂ = (l : ↥LL.1) ^ η • y₂ + (P₂.D.phi m₂ - m₂) := by
    rw [← hsum]; abel
  have hMon₂' : P₂.D.Mon (y₂' + P₂.D.phi m₂) = 0 := by
    rw [hrew, P₂.D.Mon_add_phi_sub _ (PhiMod.M_le_Man _ hm₂.1), LinearMap.map_smul, hMon₂, smul_zero]
  have hCl₂' : P₂.R.ClassOf (y₂' + P₂.D.phi m₂)
      ((l : ↥LL.1) ^ η • (l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
    rw [hrew]
    exact hpot₂.2.2.2 _ _ m₂ hm₂ (hpot₂.2.2.1 _ _ η hCl₂)

  obtain ⟨y', hy', m, hm, hMon, hGy⟩ :=
    _root_.GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple _ _ l e a _ _ _ η H P₀.D P₁.D P₂.D F G N Sig U
      ⟨hEx, hNum, hP₁, hP₂.chars_subset⟩ y₂' hy₂' m₂ hm₂ hMon₂'

  have hζ := _root_.GlobalTheory.ZetaDenominator.zetaBound _ _ l e a _ N η H Sig U hAdm P₁.D hP₁ y' hy' m hm hMon
  obtain ⟨κ₁, hκ₁, hCl₁⟩ := _root_.GlobalTheory.BKGal.classOf_of_mon_eq_zero hFon l a e ϖ LL (Fin P₁.n) η H P₁.D T₁ P₁.R Pl AI hStd hNum.lt h8
    _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.add_phi_mem_Y hy' hm) hMon _ hζ

  have hnat := _root_.GlobalTheory.CocycleNat.main l a e _ _ (thetaW a LL) ϖ (Fin P₁.n) (Fin P₂.n) η H P₁.D P₂.D T₁ T₂ P₁.R P₂.R g G hG
    _ _ hCl₁
  have happ : G.app ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig • (y' + P₁.D.phi m)) =
      (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) •
        (y₂' + P₂.D.phi m₂) := by
    have happ0 : ∀ (k : ↥LL.1) (v : Vec (↥LL.1) a (Fin P₁.n)), G.app (k • v) = k • G.app v := by
      intro k v
      ext1 τ
      simp only [Hom.app_apply, Pi.smul_apply, Matrix.mulVec_smul]
    rw [happ0, hGy, smul_smul, ← pow_add]
  rw [happ] at hnat
  have hCl := hpot₂.2.2.1 _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) hCl₂'
  rw [smul_smul, smul_smul, ← pow_add, ← pow_add] at hCl
  have hB := hpot₂.2.1 _ _ _ hnat hCl

  have hexp : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) ≤ 7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig)) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₁,
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eL, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    generalize maxPeriod l Sig = r
    have h1 : n + 2 - 1 = n + 1 := by omega
    rw [h1]
    nlinarith [Nat.zero_le (n * r), Nat.zero_le (η * n), Nat.zero_le (η * r)]
  rw [← algebraMap_smul (↥LL.1), map_pow, map_natCast, Pl.PD_p,
    ← Nat.sub_add_cancel hexp, pow_add, mul_smul]
  obtain ⟨β, hβ, hβeq⟩ : ∃ β ∈ latticeCoboundaries T₂.L, (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig)) • c = LatHom.post g κ₁ - β := ⟨_, hB, by abel⟩
  rw [hβeq, smul_sub]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hκ₁)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ hβ

end GlobalTheory.TheoremT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAtStatement
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localArtin_inertia_isUnitAt : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  first | exact @GlobalTheory.ArtinInertia.isUnitAt_artin_ine | exact GlobalTheory.ArtinInertia.isUnitAt_artin_ine | (intros; apply GlobalTheory.ArtinInertia.isUnitAt_artin_ine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertia
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.DecInertia

theorem valuation_lt_one_iff_norm {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
    {j : Ω →+* PadicAlgCl p} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (x : Ω) :
    A.valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem inertiaK_iff_mem_Ine (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p))
    (hi : ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x))
    (g : ↥(A.decompositionSubgroup F)) :
    i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hn : ∀ (σ : PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) (z : PadicAlgCl p), ‖σ z‖ = ‖z‖ := fun σ z =>
    GlobalTheory.PlaceBridge.norm_algEquiv (σ.restrictScalars ℚ_[p]) z
  have hadd : ∀ a b : PadicAlgCl p, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  constructor
  · intro h
    let H : Subgroup (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) :=
      ((Ine (F := F) A).subgroupOf (A.decompositionSubgroup F)).map i.toMonoidHom
    have hsub : Formalism.GaloisCohomology.inertiaSet p K ⊆ H := by
      intro σ hσ
      refine ⟨i.symm σ, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine ⟨(i.symm σ).2, fun x hx => ?_⟩
      rw [valuation_lt_one_iff_norm hj, map_sub, ← hi, MulEquiv.apply_symm_apply]
      exact hσ (j x) ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
    have hle : Formalism.GaloisCohomology.inertiaK p K ≤ H := (Subgroup.closure_le _).2 hsub
    obtain ⟨g', hg', e⟩ := hle h
    have : g' = g := i.injective e
    subst this
    exact Subgroup.mem_subgroupOf.1 hg'
  · intro h
    apply Subgroup.subset_closure
    intro x hx
    obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
    rw [dist_eq_norm] at hy
    have hjy : ‖j y‖ ≤ 1 := by
      have e : j y = x + -(x - j y) := by ring
      rw [e]
      exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
    have hgy : ‖(i g) (j y) - j y‖ < 1 := by
      rw [hi, ← map_sub, ← valuation_lt_one_iff_norm hj]
      exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hjy))
    have e : (i g) x - x = (i g) (x - j y) + (((i g) (j y) - j y) + -(x - j y)) := by
      rw [map_sub]; ring
    rw [e]
    refine (hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt hgy ?_)))
    rw [norm_neg]; exact hy

end GlobalTheory.DecInertia
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.CuspExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 := by
  rw [WD.lpZero, WD.charPol_mk]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree]; simp)

theorem charPol_sumList (l : List (WD h)) (σ : Weil h) :
    (GlobalTheory.LocLanglands.sumList l).charPol σ = (l.map fun y => y.charPol σ).prod := by
  induction l with
  | nil => simp [GlobalTheory.LocLanglands.sumList, charPol_lpZero]
  | cons b l ih =>
    have : GlobalTheory.LocLanglands.sumList (b :: l) =
        WD.lpSum b (GlobalTheory.LocLanglands.sumList l) := rfl
    rw [this, WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r : IrrGL (k := w.adicCompletion E) → WD h}

end GlobalTheory.LocLanglands.CuspExt

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocyclesBetweenBlochKatoAndContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_cocycles_between_blochKato_and_continuous : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v : V, Continuous fun g => ρ g v) → IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) → ∃ S : Submodule ℚ_[l] (↥(GK K) → V), finiteCocycles (P.PD K) ρ ≤ S ∧ S ≤ continuousCocycles ρ ∧ (∀ c ∈ S, ∃ z : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ (∀ c ∈ S, ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) ∧ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) ≤ finrank ℚ_[l] ↥S := by
  first | exact @GlobalTheory.PMon.exists_stCocycles_lower | exact GlobalTheory.PMon.exists_stCocycles_lower | (intros; apply GlobalTheory.PMon.exists_stCocycles_lower <;> assumption)
end

