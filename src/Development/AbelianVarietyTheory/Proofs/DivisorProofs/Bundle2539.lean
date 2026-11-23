module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.FactorPeriod


set_option maxHeartbeats 800000 in
theorem factor_period : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (W : (Sp R).Opens) (ψW : PsiOn D₀ W) (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (a b : Q.X) (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)) (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), u.IsGen → θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good Q.M.L z J → val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) → ∀ z J J', Good D₀.P.L z J → Good Q.M.L z J' → gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val u ((TK V).hom ≫ spMap θ) z J' = lamVal F.w (((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left) z J J' * val (ψW.tau (F.xi a) (F.f • F.xi b)) g z J := by
  intro R V _ _ _ _ θ Q D₀ F W ψW g hg a b u x y k k' hu hy hk hk' hτ z J J' hJ hJ'
  letI := D₀.P.isAb.comm
  obtain ⟨t, ht, tv, tl⟩ := _root_.GlobalTheory.exists_tau_onOpen R D₀ W ψW (F.xi a) (F.f • F.xi b)
  have hQ : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left ≫
      (lift (fst Q.B Q.B ≫ F.inc) (snd Q.B Q.B ≫ F.inc ≫ F.o.onB.act F.f) : G2 Q.B ⟶ G2 D₀.P.A).left =
      𝟙 _ ≫ (lift (toUnit T ≫ D₀.c (F.xi a)) (toUnit T ≫ D₀.c (F.f • F.xi b))).left := fun T => by
    rw [Category.id_comp, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, F.o.c_lin, F.c_xi, F.c_xi]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := _root_.GlobalTheory.GenTransport.gen_transport _ _ Q.B D₀.P.A Q.M.L D₀.P.L Q.M.isLB D₀.P.isLB _ F.w F.w_gen (TW W) (TW W)
    (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b) _ _ (𝟙 _) (hQ (TW W)) t ht
  obtain ⟨lam, hlam⟩ : ∃ lam : (TK R).left ⟶ W.toScheme, lam ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact GlobalTheory.TauPull.jK_mem p _ ⟨(g z).1, (g z).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have hl : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left =
      T.hom ≫ (lift (Q.c a) (Q.c b)).left := fun T => by
    rw [← comp_lift]; rfl
  have H := _root_.GlobalTheory.GenSpread.val_spread R V θ W Q.B.left Q.M.L Q.M.isLB (Fin 4) (Fin 4)
    (lamPts (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)) negε
    (fun i => W.ι ≫ lamPts (Q.c a) (Q.c b) i) negε (fun U _ h => Finset.prod_congr rfl fun i _ => by
      congr 2
      fin_cases i
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TW W)) (Q.c a) (Q.c b)).symm
      · rfl
      · rfl
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TW W))).symm)
    t₁ (LB.pullGen Q.M.L _ _ u W.ι) ht₁ (DVR.pullGen_isGen _ _ _ _ hu _) lam hlam g hg x y k k' hy hk hk'
    (fun p I' hI' => by
      obtain ⟨I, hI⟩ := DegPull.exists_good' D₀.P.isLB p
      have e₁ := v₁ _ lam p I I' hI hI'
      have e₂ : lam ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
          (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left := by
        rw [hl, hl, ← Category.assoc]
        exact congrArg (· ≫ _) hlam
      rw [e₂] at e₁
      erw [Category.comp_id] at e₁
      refine e₁.trans ((congrArg (_ * ·) (tl lam hlam p I hI)).trans ((F.tau a b p I I' hI hI').symm.trans
        ((hτ p I' hI').trans (congrArg (_ * ·) ?_))))
      rw [val_pull hI', hlam]
      rfl) z J' hJ'
  have e₁ := v₁ _ g z J J' hJ hJ'
  have e₂ : g ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
      ((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left := by
    rw [hl, ← Category.assoc]
    exact congrArg (· ≫ _) hg
  rw [e₂] at e₁
  erw [Category.comp_id] at e₁
  rw [val_pull hJ', hg] at H
  exact H.symm.trans (e₁.trans (congrArg (_ * ·) (tv _ g z J hJ)))

end GlobalTheory.FactorPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorProjectionAdjointPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

theorem factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), Adj (pol D') (pol D) F.pr (F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) F.xp ((DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi) := by
  intro R _ _ I D D' F
  haveI := F.inc_hom
  haveI := F.o.onB.hom F.f
  have hm : IsMonHom (F.inc ≫ F.o.onB.act F.f) := inferInstance
  have H := _root_.GlobalTheory.MumFam.Adj.of_twisted_comp R (pol D') (pol D) F.pr (F.o.onB.act F.e) (F.o.onB.act (Star.star F.e))
    (F.inc ≫ F.o.onB.act F.f) F.xp
    (DistribSMul.toAddMonoidHom D'.toPre.X F.e) (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e))
    ((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) F.pr_hom hm
    (fun y => c_xp F y) (fun z => c_fxi F z) (_root_.GlobalTheory.MumFam.adj_act R I D' F.O F.o F.e) (_root_.GlobalTheory.MumFam.FactorAdj.exists_pull R I D D' F)
  have e1 : (F.inc ≫ F.o.onB.act F.f) ≫ F.o.onB.act (Star.star F.e) = F.inc ≫ F.o.onB.act (Star.star F.e * F.f) := by
    rw [F.o.onB.map_mul, Category.assoc]
  have e2 : (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e)).comp
      ((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) =
      (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi := by
    ext y
    simp [mul_smul]
  exact e1 ▸ e2 ▸ H

end GlobalTheory.MumFam.FactorAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImHermFormAlternatingNondegenerateOnLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.im_hermForm_alternating_nondegenerate_on_lattice : ∀ (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Function.Injective P → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := by
  first | exact @GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate | exact GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate | (intros; apply GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.MixHt

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem divOfRatSec_congr {B : LB Y} (hB : B.IsLB) {t t' : B.ι → Y.functionFieldˣ} (ht : IsRatSec B t)
    (ht' : IsRatSec B t') (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) :
    divOfRatSec hB ht = divOfRatSec hB ht' :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨c, hc⟩ := exists_chart hB z
    refine ⟨t c, (presents_divOfRatSec hB ht).isEqn c z hc, ?_⟩
    rw [e c (gen_mem hc)]
    exact (presents_divOfRatSec hB ht').isEqn c z hc

theorem logNorm_congr {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B) {t t' : B.ι → Y.functionFieldˣ}
    (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) (y : CxPts q σ) : logNorm φ t y = logNorm φ t' y := by
  rw [logNorm, logNorm, e _ (gen_mem (mem_ptsIn.1 (mem_pick φ.isLB y)))]

theorem logNorm_tens_mul {σ : k →+* ℂ} (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (hu : IsRatSec A.B u) {y : CxPts q σ}
    (hyr : y ∈ offSupp q σ (M.div hr)) (hyu : y ∈ offSupp q σ (A.div hu)) :
    logNorm ((M.tens A).φ σ) (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) y =
      logNorm (M.φ σ) r y + logNorm (A.φ σ) u y := by
  obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 (mem_pick ((M.tens A).φ σ).isLB y)
  have hu₁ := hr.unitAt M.isLB hyr h₁
  have hu₂ := hu.unitAt A.isLB hyu h₂
  rw [logNorm_eq (M.φ σ) hr hyr h₁, logNorm_eq (A.φ σ) hu hyu h₂]
  change Real.log ‖ratVal ((r (pick ((M.tens A).φ σ).isLB y).1 * u (pick ((M.tens A).φ σ).isLB y).2 :
      Y.functionFieldˣ) : Y.functionField) y‖ - ((M.φ σ).φ (pick ((M.tens A).φ σ).isLB y).1 y +
      (A.φ σ).φ (pick ((M.tens A).φ σ).isLB y).2 y) / 2 = _
  rw [Units.val_mul, ratVal_mul hu₁.regAt hu₂.regAt, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hu₁)) (norm_ne_zero_iff.2 (ratVal_ne_zero hu₂))]
  ring

theorem chernInt_eq_of_null {D : ℕ} (hY : IsArithVar q D) {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B)
    {S S' : Set (CxPts q σ)} (hS : S ⊆ S') (Z : Set Y) (hZ : IsClosed Z) (hg : genericPoint Y ∉ Z)
    (hd : S' \ S ⊆ {y | under y ∈ Z}) (f : CxPts q σ → ℝ) : φ.chernInt D S' f = φ.chernInt D S f := by
  have h (ε : ℤˣ) : S' =ᵐ[φ.chernPart D ε] S := ae_eq_set.2
    ⟨measure_mono_null hd (ChernNull.chernPart_over_closed hY Z hZ hg σ φ ε), by
      rw [Set.diff_eq_empty.2 hS]; exact measure_empty⟩
  rw [Weight.chernInt, Weight.chernInt, setIntegral_congr_set (h 1), setIntegral_congr_set (h (-1))]

theorem chernInt_tens {D : ℕ} (hY : IsArithVar q D) (σ : k →+* ℂ) {B : LB Y} (φ : Weight q σ B)
    (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2)
    (h₁ : φ.ChernIntegrableOn D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r))
    (h₂ : φ.ChernIntegrableOn D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u)) :
    φ.chernInt D (offSupp q σ ((M.tens A).div ht)) (logNorm ((M.tens A).φ σ) t) =
      φ.chernInt D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r) +
        φ.chernInt D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u) := by
  let S := offSupp q σ (M.div hr) ∩ offSupp q σ (A.div hu) ∩ offSupp q σ ((M.tens A).div ht)
  let Z : Set Y := ((M.div hr).supp : Set Y) ∪ (A.div hu).supp ∪ ((M.tens A).div ht).supp
  have hZ : IsClosed Z :=
    ((M.div hr).supp.isClosed.union (A.div hu).supp.isClosed).union ((M.tens A).div ht).supp.isClosed
  have hg : genericPoint Y ∉ Z := by
    simp only [Z, Set.mem_union, SetLike.mem_coe, not_or]
    exact ⟨⟨CartierDiv.genericPoint_notMem_supp _, CartierDiv.genericPoint_notMem_supp _⟩,
      CartierDiv.genericPoint_notMem_supp _⟩
  have hd (T : Set (CxPts q σ)) : T \ S ⊆ {y | under y ∈ Z} := fun y hy => by
    by_contra hz
    simp only [Set.mem_setOf_eq, Z, Set.mem_union, SetLike.mem_coe, not_or] at hz
    exact hy.2 ⟨⟨mem_offSupp.2 hz.1.1, mem_offSupp.2 hz.1.2⟩, mem_offSupp.2 hz.2⟩
  have hSm : MeasurableSet S :=
    (((isOpen_offSupp _).inter (isOpen_offSupp _)).inter (isOpen_offSupp _)).measurableSet
  have hsT : S ⊆ offSupp q σ ((M.tens A).div ht) := fun _ h => h.2
  have hsM : S ⊆ offSupp q σ (M.div hr) := fun _ h => h.1.1
  have hsA : S ⊆ offSupp q σ (A.div hu) := fun _ h => h.1.2
  rw [chernInt_eq_of_null hY φ hsT Z hZ hg (hd _),
    chernInt_eq_of_null hY φ hsM Z hZ hg (hd _) (logNorm (M.φ σ) r),
    chernInt_eq_of_null hY φ hsA Z hZ hg (hd _) (logNorm (A.φ σ) u),
    Weight.chernInt_congr hSm (g := fun y => logNorm (M.φ σ) r y + logNorm (A.φ σ) u y) ?_]
  · exact Weight.chernInt_add ⟨h₁.1.mono_set fun _ h => h.1.1, h₁.2.mono_set fun _ h => h.1.1⟩
      ⟨h₂.1.mono_set fun _ h => h.1.2, h₂.2.mono_set fun _ h => h.1.2⟩
  · intro y hy
    rw [logNorm_congr _ htu y]
    exact logNorm_tens_mul M A hr hu hy.1.1 hy.1.2

theorem archInt_tens (hAI : ArchInteg) {e : ℕ} (hY : IsArithVar q e) (N M A : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2) :
    N.archInt (M.tens A) e ht = N.archInt M e hr + N.archInt A e hu := by
  have := hY.finite_emb
  unfold HermLB.archInt
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun σ => chernInt_tens hY σ (N.φ σ) M A hr hu ht htu
    (hAI k Y q e hY M N r hr σ) (hAI k Y q e hY A N u hu σ)

theorem archInt_of_isEmpty (hE : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (N M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (e : ℕ) : N.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine (finsum_congr fun σ => ?_).trans finsum_zero
  have := hE σ
  rw [Weight.chernInt, Set.eq_empty_of_isEmpty (offSupp q σ (M.div hr))]
  simp only [Measure.restrict_empty, integral_zero_measure, sub_zero]

theorem isArithVar_or_isEmpty (hq : IsAmb q) {e : ℕ} (he : topologicalKrullDim Y = (e + 1 : ℕ)) :
    IsArithVar q e ∨ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ) := by
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · refine .inr fun σ => ⟨fun y => ?_⟩
    let f : Γ(Y, ⊤) →+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp y.1.appTop.hom
    have h0 : (ℓ : ℂ) = 0 := by rw [← map_natCast f, CharP.cast_eq_zero, map_zero]
    exact hℓ.ne_zero (Nat.cast_eq_zero.1 h0)
  · have := CharP.charP_to_charZero Γ(Y, ⊤)
    exact .inl ⟨hq.1, hq.2, ‹_›, hq.3, (flat_int_iff_charZero _).2 this, he⟩

theorem pol_add {ι : Type} [Fintype ι] (a b : (ι → ℤ) → ℝ) :
    FibreProj.pol (fun n => a n + b n) = FibreProj.pol a + FibreProj.pol b := by
  simp only [FibreProj.pol, mul_add, Finset.sum_add_distrib]

theorem finsum_mult_add [IsLocallyNoetherian Y] [CompactSpace Y] (D E : CartierDiv Y) (h : Y → ℝ) :
    ∑ᶠ z, ((D + E).mult z : ℝ) * h z = ∑ᶠ z, (D.mult z : ℝ) * h z + ∑ᶠ z, (E.mult z : ℝ) * h z := by
  have hfin (D : CartierDiv Y) : (Function.support fun z => (D.mult z : ℝ) * h z).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  exact finsum_add_distrib (hfin D) (hfin E)

theorem recVal_tens : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (h : Y → ℝ) (L : Fin e → HermLB q) (M A : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (u : A.B.ι → Y.functionFieldˣ) (hu : IsRatSec A.B u) (t : (M.tens A).B.ι → Y.functionFieldˣ) (ht : IsRatSec (M.tens A).B t), (∀ (i : M.B.ι) (j : A.B.ι), genericPoint Y ∈ M.B.U i → genericPoint Y ∈ A.B.U j → t (i, j) = r i * u j) → recVal h L (M.tens A) ht = recVal h L M hr + recVal h L A hu := by
  intro hAI k _ Y _ _ q hq e he h L M A r hr u hu t ht htu
  have := hq.isNoetherian
  have htu' : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2 :=
    fun c hc => htu c.1 c.2 hc.1 hc.2
  have hdiv : (M.tens A).div ht = M.div hr + A.div hu :=
    (divOfRatSec_congr _ ht (PtHtComb.isRatSec_tens hr hu) htu').trans (PtHtComb.div_tens M A hr hu)
  have hmix : mixArch L (M.tens A) ht = mixArch L M hr + mixArch L A hu := by
    rcases isArithVar_or_isEmpty hq he with hY | hE
    · unfold mixArch
      rw [← add_div, ← pol_add]
      congr 2
      funext n
      exact archInt_tens hAI hY (comb L n) M A hr hu ht htu'
    · have h0 (N' : HermLB q) {r' : N'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N'.B r') :
          mixArch L N' hr' = 0 := by
        simp [mixArch, archInt_of_isEmpty hE, FibreProj.pol]
      rw [h0, h0, h0, add_zero]
  unfold recVal
  rw [hdiv, finsum_mult_add, hmix]
  ring

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserGeneratedDiagAntidiag
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

theorem gen_diag_anti : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.W),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PAnti σ G.W → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hv H hD hA g hg
  obtain ⟨p, hpK, hpD, hpgK, hbig⟩ := GlobalTheory.T.exists_diagonalStabiliser_mul_mem_bigCell_inert σ B G.W _ _ hT.base hT.geo.hW v w hv g hg
  obtain ⟨q, hqK, hqA, p', hp'K, hp'D, he⟩ := GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell σ G.W v (hT.base.inert v w hv).1 (p * g) hpgK hbig
  have hg' : g = p⁻¹ * (q * p') := by rw [← he]; group
  rw [hg']
  exact H.mul_mem (H.inv_mem (hD p hpK hpD)) (H.mul_mem (hA q hqK hqA) (hD p' hp'K hp'D))

end GlobalTheory.DblVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerFixesVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph

theorem vac_fixed' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (G.M'.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hv k hk
  obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ B a a' G X om om' hTr v k hk.1 _ hSB
  have h1 := GlobalTheory.T.unitaryStabilizer_preserves_vacuumCondition_at_place F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB φ₁ hφ₁ hact hvac
  obtain ⟨c, rfl⟩ := GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul F E σ B a a' G X om om' hTr v w hw θ hθ hvac φ₁ hφ₁ h1
  have hc := GlobalTheory.T.weil_vacuum_scalar_eq_one_inert_place F E σ B a a' G X om om' hTr v w hw hv k hk c hact
  rwa [hc, one_smul] at hact

end GlobalTheory.InertSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeftStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @GlobalTheory.InertSphLeft.vac_fixed_left | exact GlobalTheory.InertSphLeft.vac_fixed_left | (intros; apply GlobalTheory.InertSphLeft.vac_fixed_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaFamilyOverDegenerationFamilyPullbac
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.UpExt

theorem over_famPull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  intro R _ _ I D k F₀ E F _ _ _ _ _ _ s h α
  have hL := D.P.isLB
  have g1 : ∀ {W : Scheme.{0}} (w : W), gs (𝟙 W) w ⊤ (1 : Γ(W, ⊤)) = 1 := fun w => by
    rw [gs_eq _ w ⊤ trivial, map_one, map_one]
  have h1 := (secScal_iff_val hL _ _ _ _).1 (h α)
  refine (secScal_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  have e1 : (𝟙 _ ≫ (DegPre.prB D F).left) = (famMap D E F).left ≫ (𝟙 _ ≫ (DegPre.prB D E).left) := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, famMap_snd]
  have e2 : (𝟙 _ ≫ (famMap D E F).left) = (famMap D E F).left ≫ 𝟙 _ := by
    rw [Category.id_comp, Category.comp_id]
  change _ = _ * sval (termPull D E F k α (s.s α)) _ y J
  rw [g1, _root_.one_mul, show sval (termPull D E F k α (s.s α)) (𝟙 _) y J =
      sval (s.s α) (𝟙 _ ≫ (famMap D E F).left) y J from sval_pullOver _ _ _ _ hJ, e1, e2, GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ,
    GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ, h1 _ _ (fun ψ => hJ _), g1, _root_.one_mul]

end GlobalTheory.Mum.UpExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantsOfTrivialOnThickenings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.InvAlg

theorem invariants_of_trivial_on_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' ∧ ∃ f : C, f - 1 ∈ (maximalIdeal R).map (algebraMap R C) ∧ (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) ∧ (∀ t : TensorProduct R C R', Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) ∧ ∀ e, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C))) := by
  intro R _ _ _ hR R' _ _ _ _ hinj hGal C' _ _ _ _ _ act hact O _ _ _ _ i hi1 hi2 hi3 C hC
  haveI : IsNoetherianRing R := hR.1
  haveI : Finite (Gal (algebraMap R R')) := hGal.1
  haveI : Algebra.FiniteType R C' := Algebra.FiniteType.trans (S := R') inferInstance inferInstance
  obtain ⟨hft, hfin⟩ := GlobalTheory.T.finiteType_invariants_finite_group_and_finite R C' (Gal (algebraMap R R')) act C hC
  have hg := _root_.GlobalTheory.InvAlg.completion_invariants_agree R hR R' hinj hGal C' act hact O i hi1 hi2 hi3 C hC hft hfin
  choose gm hgc using hg
  obtain ⟨hs, hinj'⟩ := _root_.GlobalTheory.quot_tensor_level R (maximalIdeal R) R' C' O i hi3 C gm hgc
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  obtain ⟨f, hf1, hf2, hf3⟩ := _root_.GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal C ((maximalIdeal R).map (algebraMap R C)) (TensorProduct R C R') C' _ hs hinj'
  have hL : ∀ t, Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine ⟨hft, hfin, f, hf1, fun x => ⟨1, ?_⟩, fun t ht => ⟨1, ?_⟩, fun e => ⟨gm e⟩⟩
  · obtain ⟨t, ht⟩ := hf2 x
    exact ⟨t, by rw [← hL]; simpa using ht⟩
  · have := hf3 t (by rw [hL]; exact ht)
    rw [pow_one]
    rwa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this

end GlobalTheory.InvAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedTrivialLocusRigidifiedBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivLocus_closed : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A _ L₀ N hA hL₀ hamp hN hrig
  obtain ⟨Z, i, hi, hZ⟩ := _root_.GlobalTheory.closedSubscheme_glue S (TrivCond A N) (trivCond_comp A N)
    (GlobalTheory.T.lineBundleTrivialOnPullbackSquares_of_local S A N hA hN hrig) (_root_.GlobalTheory.TrivLocusLocal.exists_closed_triv_local S A L₀ N hA hL₀ hamp hN hrig)
  refine ⟨Z, i, hi, fun T t A' _ φ' hP => ?_⟩
  rw [trivCond_iff A N T t A'.left φ' A'.hom hP.1]
  exact hZ T t

end GlobalTheory.TrivLocus
end

