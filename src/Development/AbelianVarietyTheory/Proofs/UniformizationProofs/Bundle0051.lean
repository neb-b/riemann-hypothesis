module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralFamilyPrescribedTermUnitAtPrime
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanPullDegeneration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanGenerateValuationRings
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamGen

open GlobalTheory.FamSpan GlobalTheory.FieldBaseChange

theorem constVal_mul {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    constVal q z (a * b) = constVal q z a * constVal q z b := by
  rw [constVal, map_mul, gs_mul q z ⊤ trivial]; rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem comb_term {S : Type} [CommRing S] (σ : R →+* S) (ιF : S →+* F)
    (ρ : TF (R := R) F ⟶ Over.mk (specOf σ)) (hρ : ρ.left = specOf ιF) (k : ℕ) (α : D.X) {m : ℕ}
    (b g : Fin m → D.SecB k α)
    (hb : IsSecBasis (T := Over.mk (specOf σ)) (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k)
      (b i) (snd (Over.mk (specOf σ)) D.P.A).left))
    (r : Fin m → R) (hr : ∀ i, IsUnit (σ (r i)))
    (hg : ∀ i j, (g i).f j = resTop _ (scal D.P.A.hom (r i)) * (b i).f j)
    (G : Fin m → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (hG : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (G i) (D.famφB α)
      (DegPre.famε k) (g i) (DegPre.prB D F).left 1)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (sg : LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k)))
    (hsg : GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s
      (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k) sg (ρ ▷ D.P.A).left 1) :
    ∃ c : Fin m → S, ∀ j, s.f j = ∑ i, resTop _ (DVR.gF D F (ιF (c i))) * (G i).f j := by
  obtain ⟨c, hc, -⟩ := hb sg
  choose u hu using fun i => (hr i).exists_left_inv
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i,
    IntegralCoord.lin_of_sval D.P.isLB _ G fun y J hJ => ?_⟩
  have a₁ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (snd (Over.mk (specOf σ)) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_snd]
  have a₂ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (fst (Over.mk (specOf σ)) D.P.A).left =
      (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hρ, Category.assoc]
  have a₃ : (𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF) ≫ specOf σ := by
    rw [← a₂, ← a₁]
    simp only [Category.assoc]
    rw [Over.w (snd (Over.mk (specOf σ)) D.P.A)]
    exact congrArg _ (congrArg _ (Over.w (fst (Over.mk (specOf σ)) D.P.A)).symm)
  rw [← secScal_sval hsg _ y hJ]
  refine (sval_lin (fun i => scal (fst (Over.mk (specOf σ)) D.P.A).left
    ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i))) _ (fun j => (hc j).trans (Finset.sum_congr rfl fun i _ =>
      congrArg₂ (· * ·) (congrArg _ (congrArg _ (Iso.hom_inv_id_apply _ _).symm)) rfl)) _ y hJ).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  have e₃ : sval (g i) (𝟙 _ ≫ (DegPre.prB D F).left) y J =
      gs (𝟙 _ ≫ (DegPre.prB D F).left) y ⊤ (scal D.P.A.hom (r i)) * sval (b i) (𝟙 _ ≫ (DegPre.prB D F).left) y J := by
    have hm := hJ.mem (D.famφB α) (𝟙 _ ≫ (DegPre.prB D F).left)
    exact (congrArg (gs _ y _) (hg i _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hm _) rfl))
  have e₄ : gs (𝟙 _) y ⊤ (DVR.gF D F (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i))) =
      constVal (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y
        (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i)) :=
    gs_scal (fst (TF (R := R) F) D.P.A).left _ y _
  rw [sval_pullSec _ _ _ _ _ y hJ, a₁, ← secScal_sval (hG i) _ y hJ, e₃, e₄, gs_scal, gs_scal, a₂, a₃,
    constVal_specMap, constVal_specMap, constVal_specMap, ← _root_.mul_assoc, ← constVal_mul, ← map_mul,
    _root_.mul_assoc _ (u i), hu, _root_.mul_one]

theorem zero_term {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ψ : K → (Y' ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} {g : LB.Sec (LB.LinComb L φ ε)} (hg : ∀ j, g.f j = 0)
    {G : LB.Sec (LB.LinComb L ψ ε)} (hG : GeneratorPullback.SecScal L ψ ε G φ ε g h 1) (j) : G.f j = 0 := by
  refine sec_ext_val hL (s' := DVR.SecOps.secZero) (fun y J hJ => ?_) j
  rw [← secScal_sval hG _ y hJ, DVR.UUA.sval_zero_of hg _ y J (hJ.mem _ _),
    DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]


open DVR in
theorem exists_span_generate : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F₁ : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F₁ i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F₁) = ⊤ ∧ (∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ s : Fam D.toPre F k, (∃ g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1)) → ∃ c : Fin n → S, ∀ α, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (ιF (c i)))) := by
  intro hP hG hT R R' _ _ _ _ I hA φ D D' hD k hk
  classical
  have : IsNoetherianRing R := hA.1
  let pt : (TK R').left := genericPoint (Spec (CommRingCat.of (FractionRing R')))
  let P : Spec (CommRingCat.of R) := (jK R' ≫ specOf φ) pt
  have hPW : P ∈ hD.W := by
    show (jK R' ≫ specOf φ) pt ∈ hD.W
    rw [← hD.g_comm]
    exact (hD.g pt).2
  have hne : ∀ r : R, r ∉ P.asIdeal → algebraMap R' (FractionRing R') (φ r) ≠ 0 := fun r hr h => hr (by
    show algebraMap R' (FractionRing R') (φ r) ∈ PrimeSpectrum.asIdeal pt
    rw [h]; exact Ideal.zero_mem _)
  have hgen : genericPoint (Spec (CommRingCat.of R)) ∈ hD.W :=
    (genericPoint_specializes P).mem_open hD.W.isOpen hPW
  have := P.isPrime
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D'.X k hk
  choose b hb using fun α => GlobalTheory.TwistLoc.exists_basis_off_prime hP hG hT R D.toPre ⟨hD.W, hgen, ⟨hD.psiW⟩⟩ P.asIdeal k hk α
  choose r hr F f hF hfρ hf0 using fun q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g) =>
    integralFamily_at_prime hG R I hA D hD.W ⟨hD.psiW⟩ P hPW k hk (hD.xe (e q.1)) (b (hD.xe (e q.1)) q.2)
  choose f' hf' using fun q x => (SecPull.existsUnique_secPull _ _ _ _ D.toPre.P.L D'.P.L _ D.toPre.P.isLB D'.P.isLB
    hD.w hD.w_gen (Fin 4) (D'.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (famφB_comm hD x)
    (f q (hD.xe x))).exists
  choose F' hF' using fun q => exists_fam_of_isPullDeg hG R R' φ D.toPre D' hD k (F q) (f q) (f' q) (hF q) (hf' q)
  let en := (finProdFinEquiv (m := k ^ Module.finrank ℤ D'.X) (n := k ^ D.toPre.P.g)).symm
  have hoff : ∀ i i' l, i' ≠ i → ∀ j, (f (i', l) (hD.xe (e i))).f j = 0 := fun i i' l hi =>
    hf0 (i', l) _ fun mu hmu => hi ((he (e i)).unique ⟨hD.xe.symm mu, hD.xe.injective (by
      rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply]; exact hmu.symm)⟩ ⟨0, by rw [smul_zero, add_zero]⟩)
  refine ⟨_, fun i => F (en i), fun i => f (en i), fun i => F' (en i), fun i => f' (en i),
    fun i => ⟨hF _, hF' _, hf' _⟩, ?_, ?_⟩
  · have hrange : Set.range (fun i => F' (en i)) = Set.range F' := en.surjective.range_comp F'
    rw [hrange, eq_top_iff]
    rintro s -
    choose c hc using fun i => span_term hD k (e i) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
      (hb _ _ _ (fun t ht => (hne t ht).isUnit) _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hne _ (hr (i, l)))
      (fun l => hfρ (i, l)) (fun l => f' (i, l) (e i))
      (fun l y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i, l) (e i)) _ y hJ hJ')
      (fun l => (F' (i, l)).s (e i)) (fun l => hF' (i, l) (e i)) (s.s (e i))
    have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), c q.1 q.2 • F' q := by
      refine fam_ext fun χ j => ?_
      obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
      refine fam_eq_on_class_of_eq hG R' D' _ k s _ (e i) (fun j => ?_) m j
      rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
      · rfl
      · intro i' _ hi
        refine Finset.sum_eq_zero fun l _ => ?_
        have h0 := zero_sec D.toPre.P.isLB D'.P.isLB (DegPre.prB D' (FractionRing R')).left (f (i', l) (hD.xe (e i)))
          (hoff i i' l hi) (f' (i', l) (e i))
          (fun y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i', l) (e i)) _ y hJ hJ')
          ((F' (i', l)).s (e i)) (hF' (i', l) (e i)) j
        rw [smul_f, h0, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · rintro S _ _ _ σ E _ _ ιE - ρ hρ E' _ _ π hπ hπσ s ⟨sg, hsg⟩
    have hun : ∀ t : R, t ∉ P.asIdeal → IsUnit (σ t) := fun t ht => hπ.map_nonunit _ (by
      rw [hπσ]
      exact ((hne t ht).isUnit).map _)
    choose θ hθ using fun q => FamBaseChange.main hG R I D k (F q) (f q) (hF q) E
    choose c hc using fun i => comb_term σ ιE ρ hρ k (hD.xe (e i)) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
      (hb _ _ _ hun _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hun _ (hr (i, l))) (fun l => hfρ (i, l))
      (fun l => (θ (i, l)).s (hD.xe (e i))) (fun l => hθ (i, l) _) (s.s (hD.xe (e i))) (sg _) (hsg _)
    have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), ιE (c q.1 q.2) • θ q := by
      refine fam_ext fun χ j => ?_
      obtain ⟨i, ⟨m, hm⟩, -⟩ := he (hD.xe.symm χ)
      obtain rfl : χ = hD.xe (e i) + k • hD.xe m := by
        rw [← map_nsmul, ← map_add (f := _), ← hm, AddEquiv.apply_symm_apply]
      refine fam_eq_on_class_of_eq hG R D.toPre _ k s _ (hD.xe (e i)) (fun j => ?_) _ j
      rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
      · rfl
      · intro i' _ hi
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [smul_f, zero_term D.toPre.P.isLB (hoff i i' l hi) (hθ (i', l) _) j, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [← en.sum_comp] at hs
    refine ⟨fun i => c (en i).1 (en i).2, fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
    refine (sval_lin (fun i => gF D.toPre E (ιE (c (en i).1 (en i).2))) (fun i => (θ (en i)).s α)
      (fun j => (congrArg (fun t : Fam D.toPre E k => (t.s α).f j) hs).trans (sum_f _ _ α j)) _ y hJ).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    rw [secScal_sval (hθ (en i) α) _ y hJ]
    rfl

end GlobalTheory.FamGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsPullDegId
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcData

theorem unit_ext_field {K F : Type} [Field K] [Field F] (ρ : Sp F ⟶ Sp K) (z : Sp F) {U : (Sp K).Opens}
    {a b : Γ(Sp K, U)ˣ} (h : ρ z ∈ U → gm ρ z U a = gm ρ z U b) : a = b := by
  have sK : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  by_cases hz : ρ z ∈ U
  · obtain rfl : U = ⊤ := top_le_iff.1 fun y _ => by rw [Subsingleton.elim y (ρ z)]; exact hz
    have e := congrArg Units.val (h hz)
    rw [gm_val ρ z ⊤ hz, gm_val ρ z ⊤ hz] at e
    have hK : IsField Γ(Sp K, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
    letI := hK.toField
    exact Units.ext (RingHom.injective
      (((Sp F).presheaf.germ (ρ ⁻¹ᵁ ⊤) z hz).hom.comp (ρ.app ⊤).hom) e)
  · exact unit_ext fun y hy => absurd (by rw [Subsingleton.elim (ρ z) y]; exact hy) hz

variable {R : Type} [CommRing R] [IsDomain R]

theorem mapsAt_of_genRel {D D' : DegPre R} {B₀ : Scheme.{0}} {M₀ : LB B₀} (hM₀ : M₀.IsLB) {φ : D.P.A.left ⟶ B₀}
    {Φ : D'.P.A.left ⟶ D.P.A.left} {w : LB.Iso D.P.L (M₀.pull φ)} {wD : LB.Iso D'.P.L (D.P.L.pull Φ)}
    {w' : LB.Iso D'.P.L (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') {F : Type} [Field F] (ρ : Sp F ⟶ (TK R).left)
    (x : D'.X) (y : D.X) (hx : D'.xK x ≫ Φ = D.xK y) {pt₀ : PUnit → (Sp F ⟶ B₀)}
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ (fun _ => -1))) (s : F)
    (h : GenRel w (LB.pullGen _ _ _ (D.psi y) ρ) t₀ s) (h' : GenRel w' (LB.pullGen _ _ _ (D'.psi x) ρ) t₀ s) :
    ∃ b : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => D'.xK x ≫ Φ) (fun _ => -1)),
      GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit) (fun _ => Φ) wD (D'.xK x) (-1) (D'.psi x) b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J → val b r z J = val (D.psi y) r z J := by
  obtain ⟨b, -, vb⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => D'.xK x ≫ Φ) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) hx.symm) (D.psi y) (D.psi_gen y)
  refine ⟨b, fun jN jL => ?_, vb⟩
  have z : Sp F := (default : PrimeSpectrum F)
  refine unit_ext_field (K := FractionRing R) ρ z fun hz => ?_
  have mN : Φ (D'.xK x (ρ z)) ∈ D.P.L.U (jN PUnit.unit) := mem_pull.1 hz.1
  have mL : D'.xK x (ρ z) ∈ D'.P.L.U jL := hz.2
  have hp : (ρ ≫ D'.xK x) ≫ Φ = ρ ≫ D.xK y := by rw [Category.assoc, hx]
  have mN' : (ρ ≫ D.xK y) z ∈ D.P.L.U (jN PUnit.unit) := by rw [← hp]; exact mN
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (K := PUnit) (fun _ => ρ ≫ D.xK y) jN (fun _ _ _ => rfl)
    (fun _ => mN')
  obtain ⟨j₀, hj₀⟩ := exists_chart hM₀ (φ (Φ (D'.xK x (ρ z))))
  have hj₀' : φ ((ρ ≫ D.xK y) z) ∈ M₀.U j₀ := by rw [← hp]; exact hj₀
  have e := ((genRel_iff w _ t₀ s z).1 h).2 jN (fun _ => j₀) (fun _ => hj₀') (fun _ => mN')
  have e' := ((genRel_iff w' _ t₀ s z).1 h').2 (fun _ => jL) (fun _ => j₀) (fun _ => hj₀) (fun _ => mL)
  have E := Units.ext (e.trans e'.symm)
  rw [Fintype.prod_unique, Fintype.prod_unique, T _ (ρ ≫ D'.xK x) z j₀ (jN PUnit.unit) jL hj₀ mN mL, hp, mul_zpow,
    _root_.mul_assoc] at E
  have E' := mul_left_cancel E
  have a₁ := gm_pullGen D.P.L (fun _ : PUnit => D.xK y) _ (D.psi y) ρ (𝟙 _) z jN (Set.mem_iInter.2 fun _ => mN')
  have a₂ := gm_pullGen D'.P.L (fun _ : PUnit => D'.xK x) _ (D'.psi x) ρ (𝟙 _) z (fun _ => jL)
    (Set.mem_iInter.2 fun _ => mL)
  rw [Category.id_comp] at a₁ a₂
  have v := vb _ ρ z J hJ
  rw [val_of b ρ z J jN (fun k => by rw [hx]; exact eJ k), val_of (D.psi y) ρ z J jN eJ] at v
  refine (gm_res _ z _ hz _).trans (v.trans (a₁.symm.trans (E'.trans (Eq.symm ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ ((gm_res _ z _ hz _).trans a₂.symm)))))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull ρ _ z _ hz _))

theorem exists_isPullDeg_id (D D' : DegPre R) {S₀ : Scheme.{0}} {A₀ : Over S₀} [GrpObj A₀] {M₀ : LB A₀.left}
    (hM₀ : M₀.IsLB) (rig₀ : LB.Gen (M₀.pull (eSec A₀))) {f : Sp R ⟶ S₀} {φ : D.P.A.left ⟶ A₀.left}
    {φ' : D'.P.A.left ⟶ A₀.left} (p : IsGrpPullback D.P.A A₀ f φ) (p' : IsGrpPullback D'.P.A A₀ f φ')
    (w : LB.Iso D.P.L (M₀.pull φ)) (w' : LB.Iso D'.P.L (M₀.pull φ')) (g : PGen w) (g' : PGen w')
    (r : PMaps w (K := PUnit) (fun _ => eSec D.P.A) (fun _ => eSec A₀) (fun _ => 1) D.rig rig₀ f)
    (r' : PMaps w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec A₀) (fun _ => 1) D'.rig rig₀ f)
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ φ' = (D.c (xe x)).left ≫ φ)
    (Wo : (Spec (CommRingCat.of R)).Opens) (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) (ψW : PsiOn D Wo)
    {F : Type} [Field F] (ρ : Sp F ⟶ (TK R).left)
    (hψ : ∀ x, ∃ (pt₀ : PUnit → (Sp F ⟶ A₀.left)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ (fun _ => -1))) (s : F),
      GenRel w (LB.pullGen _ _ _ (D.psi (xe x)) ρ) t₀ s ∧ GenRel w' (LB.pullGen _ _ _ (D'.psi x) ρ) t₀ s) :
    ∃ hD : IsPullDeg (RingHom.id R) D D',
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ = φ' ∧ (∀ x, hD.xe x = xe x) ∧
      ∃ w₁ : LB.Iso D'.P.L (M₀.pull ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ)),
        HEq w₁ w' ∧ Tri w hD.w w₁ := by
  have hs := specOf_id R
  have hsf : specOf (RingHom.id R) ≫ f = f := by rw [hs, Category.id_comp]
  obtain ⟨e, me, he⟩ := grpPullback_iso p'
    (((isGrpPullback_pullback D.P.A (specOf (RingHom.id R))).comp p).congr hsf rfl)
  rw [← Category.assoc] at he
  subst he
  have gp : IsGrpPullback D'.P.A D.P.A (specOf (RingHom.id R))
      (e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))).congr
      (Category.id_comp _) rfl
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  obtain ⟨wD, T⟩ := exists_cancel hM₀ w w' g g' D.P.isLB D'.P.isLB
  have hc' : ∀ x, (D'.c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      (D.c (xe x)).left := fun x => by
    apply p.1.hom_ext
    · rw [Category.assoc]; exact hc x
    · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w, Over.w, hs]; exact Category.comp_id _
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW Wo).left, gW ≫ Wo.ι = jK R :=
    ⟨IsOpenImmersion.lift Wo.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hy : jK R y = genericPoint (Spec (CommRingCat.of R)) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        show Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal y) = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
      show jK R y ∈ Wo
      rw [hy]; exact hWo), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ Wo).toScheme, lam ≫ (jK R ⁻¹ᵁ Wo).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ Wo) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) Wo).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) Wo).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) Wo).lift_fst _ _ _⟩
  refine ⟨⟨e, me, wD, (isGen_iff _).2 (T.pgen_cancel hM₀ g g'), hE, ?_, xe,
    fun x => (hc' x).trans (by rw [hs, Category.id_comp]), Wo, ψW, gW, hgW.trans (by rw [hs, Category.comp_id]),
    fun x => ?_⟩, rfl, fun _ => rfl, w', HEq.rfl, T⟩
  · refine (maps_iff wD _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf (RingHom.id R)) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf (RingHom.id R)) hE D.P.L) (fun _ => rfl)).2 ?_
    exact T.pmaps_cancel hM₀ (fun _ => hE) r (by rw [hsf]; exact r')
  · obtain ⟨pt₀, t₀, s, h, h'⟩ := hψ x
    obtain ⟨b, hb, vb⟩ := mapsAt_of_genRel hM₀ T ρ x (xe x)
      ((Category.assoc _ _ _).trans (congrArg (jK R ≫ ·) (hc' x))) t₀ s h h'
    refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (vb _ _ y J hJ).trans ?_⟩
    have v := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂] at v
    exact v.symm.trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm

end GlobalTheory.ArcData

namespace GlobalTheory

theorem arcWit_data_iso : Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ'), ∃ (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) := by
  intro h5 E _ _ _ H D l c₀ c k _ bF a O O' _ _ β β' Y Y' χ χ' W W'
  obtain ⟨s1, s2, s3, -, s5, s6⟩ := W.spec
  obtain ⟨t1, t2, t3, -, t5, t6⟩ := W'.spec
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := h5.psiOnExists _ _ (admissibleBase_powerSeries k) W'.P.D
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let κ : k →+* F := ((algebraMap (FractionRing (PowerSeries k)) F).comp (algebraMap (PowerSeries k) _)).comp
    (PowerSeries.C (R := k))
  letI : Algebra (FractionRing k) F := (IsFractionRing.lift (K := FractionRing k) (g := κ) κ.injective).toAlgebra
  have ha : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C (R := k) x)) :=
    fun x => IsFractionRing.lift_algebraMap (K := FractionRing k) (g := κ) κ.injective x
  have k₁ := (s6 F _ ha rfl).1
  have k₂ := (t6 F _ ha rfl).1
  let xe : W.P.D.toPre.X ≃+ W'.P.D.toPre.X := W.e.symm.toAddEquiv.trans W'.e.toAddEquiv
  have hxe : ∀ y, xe (W.e y) = W'.e y := fun y => congrArg W'.e (W.e.symm_apply_apply y)
  obtain ⟨hD, h₁, h₂, h₃⟩ := ArcData.exists_isPullDeg_id W'.P.D.toPre W.P.D.toPre a.D₀.P.isLB a.D₀.rig t1 s1 W'.w W.w
    ((isGen_iff _).1 t2) ((isGen_iff _).1 s2)
    ((maps_iff W'.w _ (fun _ => eSec a.D₀.P.A) _ W'.P.D.toPre.rig a.D₀.rig _ _
      (rigPull_le W'.φ _ W'.he a.D₀.P.L) (fun _ => rfl)).1 t3)
    ((maps_iff W.w _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig _ _
      (rigPull_le W.φ _ W.he a.D₀.P.L) (fun _ => rfl)).1 s3)
    xe (fun x => by
      obtain ⟨y, rfl⟩ := W.e.surjective x
      rw [hxe]
      exact (s5 y).trans (t5 y).symm) Wo hWo ψW (F := F) (jFK (R := PowerSeries k) F) (fun x => by
      obtain ⟨y, rfl⟩ := W.e.surjective x
      rw [hxe]
      exact ⟨_, _, _, k₂ y, k₁ y⟩)
  exact ⟨hD, h₁, fun x => (h₂ _).trans (hxe x), h₃⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimGenerator
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.PrimGen

open GlobalTheory.FieldBaseChange

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_lower (v : AddValuation F (WithTop ℚ)) {n : ℕ} (c : Fin n → F) :
    ∃ r : ℚ, ∀ i, (r : WithTop ℚ) ≤ v (c i) := by
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (v (c i)).untopD 0).bddBelow
  refine ⟨m, fun i => ?_⟩
  have h := hm ⟨i, rfl⟩
  cases e : v (c i) with
  | top => exact le_top
  | coe y =>
    simp only [e, WithTop.untopD_coe] at h
    exact WithTop.coe_le_coe.2 h

theorem exists_vge (U : UnifPre (maximalIdeal V) D A G) (v : AddValuation F (WithTop ℚ)) {k : ℕ}
    {σ : U.SecGF F k} {s : Fam D.toPre F k} (h : U.ExpandsG F k σ s) (α : D.toPre.X) :
    ∃ r : ℚ, VGe D F v k α (s.s α) r := by
  obtain ⟨n, c, x, -, -, hs⟩ := (expandsG_iff U F k σ s).1 h
  obtain ⟨r, hr⟩ := exists_lower v c
  refine ⟨r, n, c, fun i => (x i).2 α,
    fun i => termPull D.toPre (FractionRing V) F k α (genericTerm D k α ((x i).2 α)), fun i => ?_, hr, fun j => ?_⟩
  · exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ =>
      ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval ((x i).2 α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing V) F))))))).symm
  · exact (congrArg (chartLin (famBase D.toPre F) _ j) (hs α)).trans (map_sum (chartLin (famBase D.toPre F) _ j) _ _)

theorem exists_prim_span (hU : UUStatement) {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ}
    (hQ : QForm.IsQ D.toPre ϖ Q) [IsAlgClosed F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) :
    ∃ ϑ : Fam D.toPre F 1, Prim D Q v ϑ ∧
      ∀ s : Fam D.toPre F 1, (∃ r : ℚ, VGe D F v 1 0 (s.s 0) r) → ∃ c : F, s = c • ϑ := by
  classical
  obtain ⟨b, hli, hb, hsp⟩ := hU V ϖ hϖ D Q hQ F v hv (Or.inl inferInstance) 1 le_rfl
  have : Subsingleton (Fin (1 ^ (D.toPre.rank + D.toPre.P.g))) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ (D.toPre.rank + D.toPre.P.g)) := ⟨0, by rw [one_pow]; exact one_pos⟩
  have hsp' : ∀ s, NuGe D Q F v 1 s 0 → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ s = c • b i₀ := fun s hs => by
    obtain ⟨c, hc, e⟩ := (hsp s).1 hs
    exact ⟨c i₀, hc i₀, e.trans (Fintype.sum_subsingleton _ i₀)⟩
  refine ⟨b i₀, ⟨hb i₀, fun r hr h => ?_⟩, ?_⟩
  · obtain ⟨ζ, s', hζ, hs', e⟩ := (n1c V ϖ hϖ D Q hQ F v hv 1 le_rfl (b i₀) (hb i₀)).1 ⟨r, hr, h⟩
    obtain ⟨c, hc, rfl⟩ := hsp' s' hs'
    rw [isSmul_iff, smul_smul] at e
    have e1 : ζ * c = 1 := smul_left_injective F (hli.ne_zero i₀) (e.symm.trans (one_smul F _).symm)
    have h0 : (0 : WithTop ℚ) < v (ζ * c) := by
      rw [AddValuation.map_mul]
      exact lt_add_of_lt_of_nonneg hζ hc
    rw [e1, AddValuation.map_one] at h0
    exact lt_irrefl _ h0
  · rintro s ⟨r, hr⟩
    have h1 : NuGe D Q F v 1 s (-(|r| + 1)) := by
      rw [n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) s]
      intro α hα
      obtain rfl := Finset.mem_singleton.1 hα
      refine hr.mono ?_
      rw [QForm.Q_zero hϖ D hQ]
      have := neg_abs_le r
      simp only [Int.cast_zero, zero_div, add_zero]
      linarith
    obtain ⟨ζ, hζ0, hζ⟩ := exists_val_eq hv (r := |r| + 1) (by positivity)
    have h2 := NuGe.smul Q hζ.ge ((isSmul_iff ζ s _).2 rfl) h1
    rw [neg_add_cancel] at h2
    obtain ⟨c, -, e⟩ := hsp' _ h2
    exact ⟨ζ⁻¹ * c, by rw [mul_smul, ← e, inv_smul_smul₀ hζ0]⟩

end GlobalTheory.UT.PrimGen

namespace GlobalTheory.UT

open GlobalTheory.FieldBaseChange

theorem exists_prim_generator : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ : W0 U.toUnifPre, w₀.IsGen → ∃ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ IsGenSec A.A A.L 1 th := by
  intro hL _ _ _ hU V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U w₀ hw
  obtain ⟨ϑ, hp, hsp⟩ := PrimGen.exists_prim_span hU hϖ hQ hv
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F (k := 1) le_rfl w₀ hw
  refine ⟨e.symm ϑ, ϑ, (he _ _).2 (e.apply_symm_apply ϑ), hp, fun t => ?_⟩
  obtain ⟨σ, -, hσ⟩ := (he t _).2 rfl
  obtain ⟨c, hc⟩ := hsp _ (PrimGen.exists_vge U.toUnifPre v hσ 0)
  have ht : t = (c • e.symm ϑ : SecOver (abelianBase A F) _) :=
    e.injective (hc.trans (by rw [map_smul, e.apply_symm_apply]))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c, fun j => ?_⟩
  rw [ht]
  rfl

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordAdd
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem GlobalTheory.UU.torus_coord_add : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ thickObj R I e G) (χ : D.X) (z : T.left) (J), Good D.P.L z J → val (g.t χ) (x * y).left z J * @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J (toUnit _ ≫ D.c χ) ((Over.map (thick R I e)).map x ≫ g.pG) ((Over.map (thick R I e)).map y ≫ g.pG)) = val (g.t χ) x.left z J * val (g.t χ) y.left z J) :=
  fun hG _ _ _ _ _ _ _ _ _ g _ x y χ z J hJ => GlobalTheory.TorusCoord.val_t_mul_points g hG χ x y z J hJ
end

