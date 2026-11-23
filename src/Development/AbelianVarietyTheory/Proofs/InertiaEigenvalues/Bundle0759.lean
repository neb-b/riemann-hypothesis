module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0721

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaSubOneDivUniformiserAtLetterOfConclusions
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.AdmDssLet

open Formalism.MainNotions.LiftingTheory

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem qp_isUnit (W : LocWach PD LL O v n) (hπu : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    IsUnit (algebraMap (LetA O n) W.EE (qp W)) := by
  have := W.EE_complete
  obtain ⟨u, hu⟩ := hπu
  have hj := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _
    (Ideal.mem_span_singleton_self ((PD.p : ℕ) : W.EE)))) (↑u⁻¹ : W.EE)
  have e : algebraMap (LetA O n) W.EE (qp W) = (u : W.EE) * (((PD.p : ℕ) : W.EE) * ↑u⁻¹ + 1) := by
    rw [qp, map_add (f := _), ← hu, map_natCast]
    rw [mul_add, mul_one, mul_comm ((PD.p : ℕ) : W.EE), ← mul_assoc, Units.mul_inv, one_mul, add_comm]
  rw [e]
  exact u.isUnit.mul hj

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [letE]
  · simp [letE, Pi.single_apply, hj]

theorem letter_of_qp_pow_mem (W : LocWach PD LL O v n)
    (hqu : IsUnit (algebraMap (LetA O n) W.EE (qp W))) (T : LocLat G Qp LL O) (i : ZMod n) (Y : ℕ)
    (y : W.DD T) (hy : qp W ^ Y • y ∈ W.Nl T i) :
    (letE i : LetA O n) • y = y ∧ qp W ^ Y • y ∈ W.N T := by
  obtain ⟨m, hm, hm'⟩ := Submodule.mem_map.1 hy
  have hm'' : (letE i : LetA O n) • m = qp W ^ Y • y := hm'
  have hqYu : IsUnit (algebraMap (LetA O n) W.EE (qp W ^ Y)) := by
    rw [map_pow]; exact hqu.pow _
  refine ⟨Formalism.MainNotions.UnusedSlot35.DssRec.smul_inj (E := W.EE) _ hqYu ?_, ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, ← hm'', smul_smul, letE_mul_self]
  · rw [← hm'']; exact (W.N T).smul_mem _ hm

theorem mem_Nl_of (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (a : LetA O n)
    (x : W.DD T) (hx : (letE i : LetA O n) • x = x) (hN : a • x ∈ W.N T) : a • x ∈ W.Nl T i := by
  refine Submodule.mem_map.2 ⟨_, hN, ?_⟩
  show (letE i : LetA O n) • (a • x) = a • x
  rw [smul_smul, mul_comm, ← smul_smul, hx]

theorem mem_xListL (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (M h y' Y : ℕ)
    (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ) (hτ : Over W τ i) (ha : IsJumpV PD T.ρ τ a)
    (hwin : a ∈ Set.Icc (-(M : ℤ)) (h : ℤ)) (hj1 : y' < j) (hj2 : j ≤ Y) :
    a + (j : ℤ) ∈ Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i M h y' Y := by
  unfold Formalism.MainNotions.RamifiedCoefficientChains.xListL
  rw [Finset.mem_sort, Finset.mem_image]
  refine ⟨(a, (j : ℤ)), ?_, rfl⟩
  rw [Finset.mem_product]
  refine ⟨?_, ?_⟩
  · classical
    unfold Formalism.MainNotions.RamifiedCoefficientChains.jumpSetL
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨hwin, τ, hτ, ha⟩
  · rw [Finset.mem_Icc]; constructor <;> push_cast <;> omega

end Gen

end GlobalTheory.AdmDssLet

namespace GlobalTheory


open GlobalTheory.AdmDssLet in
theorem adm18_of_N1used : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.RamifiedCoefficientChains.adm18 D HW F := by
  intro D HW F Cm hN l _ K s LL h
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL h) := hN.2.2.2.2.2.2.2.2.1 l K s LL h
  rw [Formalism.MainNotions.UnusedSlot35.DssRec.dssLet_iff_mem _ h9]
  intro hA T Mi hi hT hJ ug hug hv cO hc i y' Y y₀ hyY hy hΔ seq h0 hrec
  have hs : s = 1 := ((HW l).W_s K s LL h).symm.trans hA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hA.2.2, h⟩
    obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
    have h2 := y.2.2
    have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
    rw [this] at h2
    exact h2

  have hgen : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have h1 := ((HW l).W K 1 LL h).gam_gen
    have h2 : ((((HW l).W K 1 LL h).s : ℕ) : WithTop ℚ) = 1 := by rw [hA.2.1]; rfl
    exact h1.trans h2
  have hug2 : ug ^ (l - 1) = (((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (l - 1) := by
    have e : ((D.loc l).PD K).p - 1 = l - 1 := congrArg (· - 1) hpl
    rw [← e]; exact hug
  have hug' : ug = ((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam :=
    GlobalTheory.units_eq_of_pow_pred_eq_of_val_one l (D.loc l) LL ug _ hug2 hv hgen
  subst hug'
  have hc' : ∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x =
      1 - (((((HW l).W K 1 LL h).χΓ ((HW l).W K 1 LL h).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL)) := by
    intro x
    have e : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) = ((l : ℕ) : ↥(OL LL)) := congrArg _ hpl
    rw [← e]; exact hc x

  have hqu := qp_isUnit _ (Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit _ h9 hA T hT)
  obtain ⟨hey, hN0⟩ := letter_of_qp_pow_mem _ hqu T i Y y₀ hy
  have hDL0 : Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL h) T i (seq 0) := by
    rw [h0]; exact ⟨hey, hΔ⟩
  rw [← h0] at hN0
  obtain ⟨hDL, hmem⟩ := GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl T hT i y' Y cO hc'
    (Formalism.MainNotions.RamifiedCoefficientChains.xListL ((HW l).W K 1 LL h) T i (Mi i) (hi i) y' Y)
    (fun τ a j hτ ha hj1 hj2 => mem_xListL _ T i (Mi i) (hi i) y' Y τ a j hτ ha (hJ i τ hτ a ha) hj1 hj2)
    seq hDL0 hN0 hrec
  exact mem_Nl_of _ T i _ _ hDL.1 hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodIdempotentIrreducibleCharacterGenericSumNeZe
section
open Formalism.BasicNotions GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.WhittakerMeets

open Formalism.L2.DIV GlobalTheory.FinGL

def addOf {p : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) : AddChar (ZMod p) ℂ where
  toFun a := (θ (Multiplicative.ofAdd a) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [ofAdd_add]

theorem addOf_ne_one {p : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) (h : θ ≠ 1) : addOf θ ≠ 1 := by
  intro h1
  apply h
  refine MonoidHom.ext fun z => Units.ext ?_
  have h2 : addOf θ (Multiplicative.toAdd z) = 1 := by rw [h1]; rfl
  exact h2

theorem addCharHom_addOf {p r : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) (h : unip (ZMod p) r) :
    ((addCharHom (addOf θ) (supHom (ZMod p) r) h : ℂˣ) : ℂ) =
      (θ (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))) : ℂ) :=
  rfl

theorem local_sum_ne_zero {p : ℕ} [hp : Fact p.Prime] {r : ℕ} [Fintype (unip (ZMod p) r)] (θ : GL (Fin r) (ZMod p) → ℂ)
    (hθ : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ) (θ' : Multiplicative (ZMod p) →* ℂˣ) (h' : θ' ≠ 1) :
    ∑ h : unip (ZMod p) r, θ h *
      (((θ' (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))))⁻¹ : ℂˣ) : ℂ)
      ≠ 0 := by
  obtain ⟨d, b, σ, hσ, hθe⟩ := hθ
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.finite_parInd (F := ZMod p) b σ
  have h1 := GlobalTheory.GenericProduct.sum_unip_eq (addOf θ') (parInd b σ)
  rw [GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one (ZMod p) (addOf θ') (addOf_ne_one θ' h') r _ b σ hσ, Nat.cast_one, mul_one] at h1
  have e : ∀ h : unip (ZMod p) r, θ h *
      (((θ' (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))))⁻¹ : ℂˣ) : ℂ) =
      LinearMap.trace ℂ _ (parInd b σ h) * (((addCharHom (addOf θ') (supHom (ZMod p) r) h)⁻¹ : ℂˣ) : ℂ) := by
    intro h
    rw [hθe, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, addCharHom_addOf]
    rfl
  rw [Finset.sum_congr rfl fun h _ => e h, h1]
  exact Nat.cast_ne_zero.2 Nat.card_pos.ne'

end GlobalTheory.WhittakerMeets

namespace GlobalTheory.WhittakerMeets

open Formalism.L2.DIV GlobalTheory.FinGL

theorem sum_ne_zero : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)] (U : Subgroup (G0g D.nd)) [Fintype U], U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r → ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ → 2 ≤ D.R.r → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0 := by
  intro D S _ U _ hU ψ hψ hr χ hχ he
  classical
  subst hU
  haveI hF : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fact (D.host.g kv.1).Prime := fun kv => ⟨D.host.g_prime kv.1⟩
  haveI hN : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), NeZero (D.host.g kv.1) := fun kv => ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨θ, hθ, hχe⟩ := GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product D (fun k => ⟨_, S.O k, S.eSer_def k⟩) χ hχ he
  obtain ⟨θ', hθ'1, hψe⟩ := hψ
  have hθ' := hθ'1 hr
  letI : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fintype (unip (ZMod (D.host.g kv.1)) D.R.r) := fun kv => Fintype.ofFinite _
  let f : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), unip (ZMod (D.host.g kv.1)) D.R.r → ℂ := fun kv h =>
    θ kv h * (((θ' kv (Multiplicative.ofAdd (Formalism.L2.NX.supSum D.R.r
      ((h : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))))⁻¹ : ℂˣ) : ℂ)
  let e : Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ≃
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), unip (ZMod (D.host.g kv.1)) D.R.r :=
    { toFun := fun u kv => ⟨u.1 kv, (u.2 kv).1, (u.2 kv).2⟩
      invFun := fun y => ⟨fun kv => (y kv).1, fun kv => ⟨(y kv).2.1, (y kv).2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hterm : ∀ u : Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r,
      χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) = ∏ kv, f kv (e u kv) := by
    intro u
    rw [hχe, hψe, Formalism.L2.NX.stdVal, ← Finset.prod_inv_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
    rfl
  rw [Finset.sum_congr rfl fun u _ => hterm u, Fintype.sum_equiv e _ (fun y => ∏ kv, f kv (y kv)) fun _ => rfl,
    ← Fintype.prod_sum]
  exact Finset.prod_ne_zero_iff.2 fun kv _ => local_sum_ne_zero (θ kv) (hθ kv) (θ' kv) (hθ' kv)

end GlobalTheory.WhittakerMeets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodProper

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}

theorem polAt_of_fibre {S Z : Scheme.{0}} {K : Type} [Field K] {t : SAB H S} {u : SAB H Z} {t' : SAB H (Sp K)}
    {x : Sp K ⟶ S} {y : Sp K ⟶ Z} (m : SABMap t' t x) (n : SABMap t' u y) (hp : IsProper u.G.hom)
    (hA : RelAmple u.G u.PP.L) (hK : KTriv u.G u.PP.L) : GlobalTheory.LN.PolAt t x := by
  have g₁ : IsGrpPullback ((Over.pullback x).obj t.G) t.G x (pullback.fst t.G.hom x) := isGrpPullback_pullback t.G x
  have w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x := by
    rw [Category.comp_id]; exact pullback.condition
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ t'.G.left,
      ψ ≫ m.φ = pullback.fst t.G.hom x ∧ ψ ≫ t'.G.hom = pullback.snd t.G.hom x ≫ 𝟙 _ :=
    ⟨_, m.cart.1.lift_fst _ _ w, m.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) t'.G (𝟙 _) ψ :=
    m.cart.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂
  have g₃ : IsGrpPullback ((Over.pullback x).obj t.G) u.G (𝟙 _ ≫ y) (ψ ≫ n.φ) := g₂.comp n.cart
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (u.PP.L.pull (ψ ≫ n.φ)) :=
    LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB t'.PP.isLB _) (pull_isLB u.PP.isLB _)
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ h₁.symm).symm
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap n) _ rfl)
  have hp' : IsProper (pullback.snd t.G.hom x) := MorphismProperty.of_isPullback (P := @IsProper) g₃.1 hp
  have hq := amplePt Z K (𝟙 _ ≫ y) u.G ((Over.pullback x).obj t.G) _ g₃ u.PP.L (t.PP.L.pull (pullback.fst t.G.hom x))
    u.PP.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom x)) e hA hK
  exact ⟨hp', hq.1, hq.2⟩

theorem isProper_of_abLocus_eq_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), abLocus G.G = Set.univ → IsProper G.G.hom := by
  intro E _ _ _ H Dw l Xo T x t t' m₁ m₂ hab
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have ht : ∀ z, z ∈ abLocus t.G := fun z => hab ▸ Set.mem_univ z
  have hW : GlobalTheory.LN.CDvr T.V := ⟨T.dvr, T.cpl, T.ch0⟩
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H T.V hW t
    (polAt_of_fibre m₂ m₁ Xo.univ.proper Xo.univ.ample Xo.univ.ktriv)
    (GlobalTheory.GoodTrait.splitOver_of_abLocus t.G t.semi ht)
  have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (T.V ⧸ maximalIdeal T.V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (T.V ⧸ maximalIdeal T.V ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick T.V (maximalIdeal T.V) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom
  exact (isAbelianScheme_of_unif_of_subsingleton l₁ l₂ T.V T.cpl P.D P.A t.G t.semi P.U hs).proper

end GlobalTheory.GoodProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransportStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_transport : GlobalArtinReciprocity → ChevalleyUnits → BrauerDegreeZero → LocalLanglandsExists → LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h'), IsRecLit h rc → IsRecLit h' rc' → FieldCompatible rc rc' := by
  first | exact @GlobalTheory.LocLanglands.FieldCompat.fieldCompatible | exact GlobalTheory.LocLanglands.FieldCompat.fieldCompatible | (intros; apply GlobalTheory.LocLanglands.FieldCompat.fieldCompatible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenWeight
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.PtExt


set_option maxHeartbeats 1000000 in
theorem main : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), Built A M C tp.tup big₀ L₀ → Built A M C tp.tup big₁ L₁ → ∀ i₁ : L₁.lay.fixZ.nd.Loc, ∃ i₀ : L₀.lay.fixZ.nd.Loc, L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧ L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ ∧ ∃ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, ∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big₀ big₁ L₀ L₁ hB₀ hB₁ i₁
  have onto : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 →
      ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w),
        ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, sys L i x = c := by
    intro big L hB j w h1 h2 htw c hc
    obtain ⟨i, hi, x, hx⟩ := _root_.GlobalTheory.EigOnto.main hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big L hB j w h1 h2 htw c hc
    refine ⟨i, hi, x, funext fun v => funext fun k => ?_⟩
    by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
    · rw [sys_of_genAt hB hi x hg, hx v k hg]
    · rw [sys_of_not_genAt hB hi x hg, hc.1 v k hg]
  have cong : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w →
      ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'),
        (i = i' ↔ ∀ v k, sys L i x v k - sys L i' x' v k ∈ (A.pl.plB w).nonunits) := by
    intro big L hB j w i i' hi hi' x x'
    rw [_root_.GlobalTheory.CoefDuty.sameLoc_iff_heckeCong D cf jE A M C tp.tup big L hB j w i i' hi hi' x x']
    constructor
    · intro h v k
      by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
      · rw [sys_of_genAt hB hi x hg, sys_of_genAt hB hi' x' hg]; exact h v k hg
      · rw [sys_of_not_genAt hB hi x hg, sys_of_not_genAt hB hi' x' hg, sub_zero]; exact zero_mem _
    · intro h v k hg
      rw [← sys_of_genAt hB hi x hg, ← sys_of_genAt hB hi' x' hg]; exact h v k
  have h1 := (L₁.X.nd.j_range i₁).1
  have h2 := (L₁.X.nd.j_range i₁).2
  have hi₁ : i₁ ∈ L₁.X.nd.locs (L₁.X.nd.j i₁) (L₁.X.nd.w i₁) := (L₁.X.nd.locs_mem _ _ i₁).2 ⟨rfl, rfl⟩
  have htw : D.what₂.muAt (L₁.X.nd.w i₁) ≠ D.what₂.mu0 := L₁.X.nd.w_tw i₁
  obtain ⟨x₁⟩ := L₁.X.nd.neX i₁
  obtain ⟨i₀, hi₀, y₀, hy₀⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (sys_mem hB₁ h1 h2 hi₁ x₁)
  have fwd : ∀ x : L₁.X.nd.X i₁, ∃ y : L₀.X.nd.X i₀, sys L₀ i₀ y = sys L₁ i₁ x := by
    intro x
    obtain ⟨i', hi', y', hy'⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (sys_mem hB₁ h1 h2 hi₁ x)
    have hc : i' = i₀ := by
      rw [cong big₀ L₀ hB₀ _ _ i' i₀ hi' hi₀ y' y₀, hy', hy₀]
      exact (cong big₁ L₁ hB₁ _ _ i₁ i₁ hi₁ hi₁ x x₁).1 rfl
    subst hc
    exact ⟨y', hy'⟩
  choose f hf using fwd
  have finj : Function.Injective f := fun x x' h => sys_inj L₁ i₁ (by rw [← hf x, ← hf x', h])
  have fsurj : Function.Surjective f := by
    intro y
    obtain ⟨i', hi', x', hx'⟩ := onto big₁ L₁ hB₁ _ _ h1 h2 htw _ (sys_mem hB₀ h1 h2 hi₀ y)
    have hc : i' = i₁ := by
      rw [cong big₁ L₁ hB₁ _ _ i' i₁ hi' hi₁ x' x₁, hx', ← hy₀]
      exact (cong big₀ L₀ hB₀ _ _ i₀ i₀ hi₀ hi₀ y y₀).1 rfl
    subst hc
    exact ⟨x', sys_inj L₀ i₀ (by rw [hf x', hx'])⟩
  have hw₀ : L₀.X.nd.w i₀ = L₁.X.nd.w i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).2
  have hj₀ : L₀.X.nd.j i₀ = L₁.X.nd.j i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).1
  refine ⟨i₀, hw₀, hj₀, Equiv.ofBijective f ⟨finj, fsurj⟩, fun v k x hv k1 k2 => ?_⟩
  have hg := (splitOut_iff_genAt hB₁ hi₁ v k).1 ⟨hv, k1, k2⟩
  have e := congrFun (congrFun (hf x) v) k
  rw [sys_of_genAt hB₀ hi₀ _ hg] at e
  exact (sys_of_genAt hB₁ hi₁ x hg).symm.trans e.symm

end GlobalTheory.PtExt

end
end

