module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfWeightSum
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0093

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.CompleteBaseExpansion
open GlobalTheory.BaseExpansionExists

section General
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem pull_le (h : Y' ⟶ Y) (j : PUnit → K → L.ι) :
    ((LB.LinComb L φ ε).pull h).U j ≤ LB.wchart L (fun k => h ≫ φ k) (j PUnit.unit) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k

theorem le_pull (h : Y' ⟶ Y) (j : K → L.ι) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull h).U (fun _ => j) :=
  fun _ hy => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)

theorem g_pull (h : Y' ⟶ Y) (y : Y') (j j' : PUnit → K → L.ι) (hj : y ∈ ((LB.LinComb L φ ε).pull h).U j)
    (hj' : y ∈ ((LB.LinComb L φ ε).pull h).U j') :
    gs (𝟙 Y') y _ (((LB.LinComb L φ ε).pull h).g j j').val =
      (trF (fun k => h ≫ φ k) ε (𝟙 Y') y (j PUnit.unit) (j' PUnit.unit)).val := by
  have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ ((LB.LinComb L φ ε).pull h).U j ⊓ ((LB.LinComb L φ ε).pull h).U j' := ⟨hj, hj'⟩
  refine (gs_unit (𝟙 Y') y _ hm _).trans (congrArg Units.val ?_)
  refine (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y j j' hj hj').trans ?_
  refine (gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans ?_
  simp only [trF, Category.assoc]

theorem exists_in (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε)) :
    ∃ s' : LB.Sec ((LB.LinComb L φ ε).pull h), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : PUnit → K → L.ι),
      r z ∈ ((LB.LinComb L φ ε).pull h).U j →
      gs r z _ (s'.f j) = gs r z (LB.wchart L (fun k => h ≫ φ k) (j PUnit.unit)) (s.f (j PUnit.unit)) := by
  refine ⟨⟨fun j => (Y'.presheaf.map (homOfLE (pull_le h j)).op).hom (s.f (j PUnit.unit)),
    fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z j hz => gs_res r z _ hz _⟩
  refine ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (pull_le h j) hy.1 _)).trans (Eq.trans ?_
    ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·) (g_pull h y j j' hy.1 hy.2)
      ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (pull_le h j') hy.2 _)))).symm)
  exact sec_trans s (𝟙 Y') y (pull_le h j hy.1) (pull_le h j' hy.2)

theorem exists_out (h : Y' ⟶ Y) (s' : LB.Sec ((LB.LinComb L φ ε).pull h)) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs r z (LB.wchart L (fun k => h ≫ φ k) j) (s.f j) =
        gs r z (((LB.LinComb L φ ε).pull h).U (fun _ => j)) (s'.f (fun _ => j)) := by
  refine ⟨⟨fun j => (Y'.presheaf.map (homOfLE (le_pull (ε := ε) h j)).op).hom (s'.f (fun _ => j)),
    fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z j hz => gs_res r z _ hz _⟩
  have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ ((LB.LinComb L φ ε).pull h).U (fun _ => j) ⊓
    ((LB.LinComb L φ ε).pull h).U (fun _ => j') := ⟨le_pull h j hy.1, le_pull h j' hy.2⟩
  refine ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (le_pull h j) hy.1 _)).trans (Eq.trans ?_
    ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ ε (𝟙 Y') y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (le_pull h j') hy.2 _)))).symm)
  exact (gs_res (𝟙 Y') y _ hm _).symm.trans ((congrArg (gs (𝟙 Y') y _) (s'.compat _ _)).trans
    ((gs_mul (𝟙 Y') y _ hm _ _).trans (congrArg₂ (· * ·) (g_pull h y _ _ hm.1 hm.2) (gs_res (𝟙 Y') y _ hm _))))

theorem gs_eq_of_sval (hL : L.IsLB) {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (s' : LB.Sec (LB.LinComb L φ' ε)) (r : Z ⟶ Y) (r' : Z ⟶ Y') (e : ∀ k, r ≫ φ k = r' ≫ φ' k) (z : Z)
    (h : ∀ J, Good L z J → sval s r z J = sval s' r' z J) (j : K → L.ι) (hj : r' z ∈ LB.wchart L φ' j) :
    gs r z (LB.wchart L φ j) (s.f j) = gs r' z (LB.wchart L φ' j) (s'.f j) := by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  have hj₀ : r z ∈ LB.wchart L φ j := Set.mem_iInter.2 fun k =>
    (congrArg (fun p : Z ⟶ X => p z ∈ L.U (j k)) (e k)).mpr (Set.mem_iInter.1 hj k)
  refine (sec_trans s r z hj₀ (hJ.mem φ r)).trans (Eq.trans ?_ (sec_trans s' r' z hj (hJ.mem φ' r')).symm)
  refine congrArg₂ (· * ·) (congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)) (h J hJ)
  beta_reduce
  rw [e k]

end General

section Levels
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

theorem exists_limit (hS : SecAlgSt) (hI : IsAdicComplete I R) (D : DegPre R) (k : ℕ) (α : D.X)
    (f : ∀ e, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)))
    (hf : ∀ e z J, Good D.P.L z J → sval (f (e + 1)) (thickMap R I e D.P.A) z J = sval (f e) (𝟙 _) z J) :
    ∃ s : LB.Sec (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)),
      ∀ e z J, Good D.P.L z J → sval s (D.prBe I e).left z J = sval (f e) (𝟙 _) z J := by
  choose f' hf' using fun e => exists_in (φ := D.famφB α) (fstG I e D.P.A).left (f e)
  obtain ⟨s', hs', -⟩ := hS R I hI D.P.A D.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.P (IsPullback.id_horiz _)) _ (DVR.linComb_isLB _ D.P.isLB _ _) f'
    fun e z J hJ => by
      refine (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I (e + 1) D.P.A).left) _)).trans
        (Eq.trans ?_ (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I e D.P.A).left) _)).symm)
      have E : thickMap R I e D.P.A ≫ (fstG I (e + 1) D.P.A).left = 𝟙 _ ≫ (fstG I e D.P.A).left :=
        (thickMap_fst e).trans (Category.id_comp _).symm
      beta_reduce
      rw [E]
      exact gs_eq_of_sval D.P.isLB _ _ _ _ (fun i => (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ D.famφB α i) E).trans (Category.assoc _ _ _))) z (hf e z) _
        (pull_le _ _ (hJ.mem (fun _ : PUnit => (fstG I e D.P.A).left) _))
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) s'
  obtain ⟨s, hs⟩ := exists_sec D.P.isLB (φ' := D.famφB α) (ε' := DegPre.famε k)
    (fun U _ h => by simp only [Category.id_comp]) s₁
  refine ⟨s, fun e z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)⟩
  have hN : Good (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)) z (fun ψ i => J (ψ ≫ D.famφB α i)) :=
    fun ψ => hJ.mem _ ψ
  refine Eq.trans ?_ ((hs' e z _ hN).trans
    ((hf' _ _ _ z _ (hN.mem (fun _ : PUnit => (fstG I e D.P.A).left) _)).trans ?_))
  · exact (sval_of s' _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
  · exact (sval_of (f e) _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm

variable {D : DegPre R} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_expT (hS' : SecAlgSt) (hI : IsAdicComplete I R) (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) :
    ∃ f, U.ExpT (𝟙_ _) k σ f := by
  have hB := D.P.isLB
  have hG := U.P.L.isLB
  have lam : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ _) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]

  have lev : ∀ e : ℕ, ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => (U.gt e).pG.left) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) JG J,
        Good U.P.L.L z JG → Good D.P.L z J →
        sval τ r z J = (gw (U.w e) r z (J (r ≫ (U.gt e).pG.left))
          (fun _ => JG (r ≫ (fstG I e G).left))).val ^ k *
          sval σ ((r ≫ (fstG I e G).left) ≫ (λ_ G).inv.left) z JG := fun e => by
    obtain ⟨s, hs⟩ := exists_pull (φ' := fun _ : Fin 1 => (fstG I e G).left)
      ((fstG I e G).left ≫ (λ_ G).inv.left)
      (fun _ => by rw [Category.assoc, lam', Category.comp_id]) σ
    obtain ⟨τ, hτ⟩ := exists_carry hG hB (U.w e) (U.w_gen e) k s
    refine ⟨τ, fun Z r z JG J hJG hJ => (hτ Z r z JG J hJG hJ).trans (congrArg _ ((hs Z r z JG hJG).trans ?_))⟩
    exact congrArg (fun p => sval σ p z JG) (Category.assoc _ _ _).symm
  choose τ hτ using lev
  have ex := fun e => existsUnique_level_expansion R I D e G (U.gt e) k (τ e)
  choose f hf hu using ex
  choose S hS hsum using hf

  have compat : ∀ α e z J, Good D.P.L z J →
      sval (f (e + 1) α) (thickMap R I e D.P.A) z J = sval (f e α) (𝟙 _) z J := by
    intro α e
    choose f' hf' using fun β => exists_pull
      (φ' := fun i => (D.prBe I e).left ≫ D.famφB β i) (thickMap R I e D.P.A)
      (fun i => ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.famφB β i) (thickMap_prBe e))).symm) (f (e + 1) β)
    have E : f' = f e := by
      refine hu e f' ⟨S (e + 1), fun β hβ => zero_of_sval hB fun y J hJ =>
        (hf' β _ _ y J hJ).trans (sval_zero (hS _ β hβ) _ hJ), fun z J hJ => ?_⟩
      obtain ⟨JG, hJG⟩ := exists_good_pt hG z
      have a := sum_of_id (hsum (e + 1)) (thickMap R I e G) z hJ
      have b : sval (τ e) (𝟙 (thickObj R I e G).left) z J =
          sval (τ (e + 1)) (thickMap R I e G) z J := by
        refine (hτ e _ _ z JG J hJG hJ).trans (Eq.trans ?_ (hτ (e + 1) _ _ z JG J hJG hJ).symm)
        have c := U.w_compat e _ (𝟙 _) z _ _ (hJ (U.gt e).pG.left) (hJG (fstG I e G).left)
        rw [Category.id_comp] at c
        rw [U.gt_q, thickMap_fst, c]
        simp only [Category.id_comp]
      refine b.trans (a.trans (Finset.sum_congr rfl fun β _ => congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
      · exact (congrArg (fun p => sval (f (e + 1) β) p z J) (q_thickMap U e).symm).trans (hf' β _ _ z J hJ).symm
      · exact ((congrArg (fun p => val ((U.gt (e + 1)).t β) p z J) (Category.id_comp _).symm).trans
          (val_pull hJ _ _ _).symm).trans (val_corr hJ (U.gt_t e β) _)
    intro z J hJ
    rw [← E]
    exact ((hf' α _ _ z J hJ).trans (congrArg (fun p => sval (f (e + 1) α) p z J) (Category.id_comp _))).symm
  choose s hs using fun α => exists_limit hS' hI D k α (fun e => f e α) (compat α)
  choose F hF using fun α => exists_pull (snd (𝟙_ _) D.P.A).left (famφT_eq (𝟙_ _) α) (s α)
  refine ⟨F, fun e => ⟨S e, fun Z x rG rB hrG hrB _ z JG J hJG hJ => ?_⟩⟩
  have v : ∀ α, sval (F α) rB z J = sval (f e α) (x ≫ (U.gt e).q.left) z J := fun α => by
    refine (hF α _ _ z J hJ).trans ?_
    have a := sval_eq_of_id (hs α e) (x ≫ (U.gt e).q.left) z hJ
    refine Eq.trans (congrArg (fun p => sval (s α) p z J) (hrB.trans (Category.assoc _ _ _).symm)) (a.trans ?_)
    exact congrArg (fun p => sval (f e α) p z J) (Category.comp_id _)
  refine ⟨fun α hα => (v α).trans (sval_zero (hS e α hα) _ hJ), ?_⟩
  have r : rG = (x ≫ (fstG I e G).left) ≫ (λ_ G).inv.left := by
    rw [← hrG, Category.assoc, lam, Category.comp_id]
  rw [r]
  refine (hτ e _ x z JG J hJG hJ).symm.trans ((sum_of_id (hsum e) x z hJ).trans ?_)
  exact Finset.sum_congr rfl fun α _ => congrArg (· * _) (v α).symm

theorem expT_unique [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (U : PreU I D A G) (k : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (f f' : ∀ α, SecBT D (𝟙_ _) k α) (h : U.ExpT (𝟙_ _) k σ f) (h' : U.ExpT (𝟙_ _) k σ f') :
    f = f' := by
  have hd := ExpUniq.expT_diff h h'
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have lam : (snd (𝟙_ _) D.P.A).left ≫ (λ_ D.P.A).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ D.P.A).inv.left ≫ (snd (𝟙_ _) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  refine funext fun α => ExpUniq.eq_of_diffSec (zero_of_sval D.P.isLB fun y J hJ => ?_)
  obtain ⟨s, hs⟩ := exists_pull (λ_ D.P.A).inv.left (fun _ => rfl) (ExpUniq.diffSec (f α) (f' α))
  have h₀ := (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.P.A).1 _ (DVR.linComb_isLB _ D.P.isLB _ _) s
    fun e j => fn_ext fun z hz => by
      have hz' : (𝟙 (thickObj R I e D.P.A).left : _ ⟶ _) z ∈ (fstG I e D.P.A).left ⁻¹ᵁ _ := hz
      refine (gs_pull (𝟙 _) (fstG I e D.P.A).left z _ hz' _).trans (Eq.trans ?_ ((gs_eq (𝟙 _) z _ hz' _).trans
        ((congrArg _ (map_zero _)).trans (map_zero _))).symm)
      refine ExpUniq.gs_eq_zero_of_sval D.P.isLB s _ z (fun J hJ => (hs _ _ z J hJ).trans ?_) j hz'
      refine ExpUniq.sval_term_eq_zero hd (fun Z r z J hJ => by rw [ExpUniq.sval_diffSec _ _ _ hJ, sub_self]) α e _
        (pullback.snd D.P.A.hom (thick R I e)) ?_ z J hJ
      rw [Category.assoc _ _ (snd (𝟙_ _) D.P.A).left, lam', Category.comp_id, Category.id_comp]
      exact pullback.condition
  have E := (hs _ (snd (𝟙_ _) D.P.A).left y J hJ).symm.trans (sval_zero h₀ _ hJ)
  rwa [lam] at E

end Levels

theorem main : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k), ∃! f : ∀ α, SecBT D (𝟙_ _) k α, U.ExpT (𝟙_ _) k σ f := by
  intro _ _ hE R _ _ _ I hR _ D A G _ _ U k σ
  have := hR.1
  have := hR.2.2.2
  exact existsUnique_of_exists_of_unique (exists_expT hE.2.2.1 hR.2.2.2 U k σ)
    (expT_unique (IsAdicComplete.le_jacobson_bot I) U k σ)

end GlobalTheory.CompleteBaseExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpandsGOfGenericRel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull GlobalTheory.ExpGTrans

section Generic

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem cst_mul_eq {R : Type} [CommRing R] (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    cst q z (a * b) = cst q z a * cst q z b := by
  rw [cst, map_mul]
  exact gs_mul q z ⊤ trivial _ _

theorem cst_comp_eq {R F : Type} [CommRing R] [CommRing F] (q : Z ⟶ Spec (CommRingCat.of F)) (φ : R →+* F) (z : Z)
    (a : R) : cst (q ≫ Spec.map (CommRingCat.ofHom φ)) z a = cst q z (φ a) := by
  refine (gs_pull q _ z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) ?_)
  exact (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem sval_scale_const {R : Type} [CommRing R] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Spec (CommRingCat.of R))
    (c : R) (t : LB.Sec (LB.LinComb L φ ε)) (q : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (SecOps.secScale (scal p c) t) q z J = cst (q ≫ p) z c * sval t q z J :=
  (gs_mul q z _ (hJ.mem _ q) _ _).trans (congrArg (· * _)
    ((gs_res q z le_top (hJ.mem _ q) _).trans (ExpInt.gs_scal p q z c)))

theorem secLin_rescale (hL : L.IsLB) {R F : Type} [CommRing R] [Field F] (ρ : R →+* F)
    {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (p : Y ⟶ Spec (CommRingCat.of R))
    {π : Y' ⟶ Spec (CommRingCat.of F)} (hp : h ≫ p = π ≫ Spec.map (CommRingCat.ofHom ρ)) {c : Fin n → F}
    (a : Fin n → R) (ha : ∀ i, ρ (a i) ≠ 0) (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h (fun i => scal π (c i))) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε (fun i => SecOps.secScale (scal p (a i)) (s i)) h
      (fun i => scal π (c i / ρ (a i))) := by
  refine (FieldBaseChange.secLin_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  rw [(FieldBaseChange.secLin_iff_val hL _ _ _ _).1 H y J hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval_scale_const _ _ _ _ _ hJ, ExpInt.gs_scal, ExpInt.gs_scal, Category.assoc, hp, ← Category.assoc, cst_comp_eq,
    ← _root_.mul_assoc, ← cst_mul_eq, div_mul_cancel₀ _ (ha i)]

end Generic

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem expansion_eq (hR : AdmBase R I) (U : UnifPre I D A G) {k : ℕ} {σ : H0 U.LG.L k}
    {f g : ∀ α, D.toPre.SecB k α} (hf : ∀ e, U.ExpandsAt e k σ f) (hg : ∀ e, U.ExpandsAt e k σ g) : f = g := by
  have s : ∀ {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) (a b : Γ(Y, W)),
      resTop W (scal p 1) * a + resTop W (scal p (-1)) * b = a - b := fun p W a b => by
    simp only [scal, map_neg, map_one, resTop]
    ring
  have h := (comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k 2 ![1, -1] (fun _ => σ) ![f, g]
    (fun i => by fin_cases i; exacts [hf, hg])).1 fun j => by
      rw [Fin.sum_univ_two]; exact (s _ _ _ _).trans (sub_self _)
  funext α
  refine SecOps.sec_ext fun j => sub_eq_zero.1 ((s D.toPre.P.A.hom _ _ _).symm.trans ?_)
  have := h α j
  rwa [Fin.sum_univ_two] at this

theorem LevelIso.exists_expansion (hG : GlobalFnsSt) (hR : AdmBase R I) {U : Unif I D A G} {U' : Unif I D' A' G'}
    {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j) {k : ℕ} (hk : 1 ≤ k) (τ : H0 U.LG.L k)
    (f : ∀ α, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k τ f) :
    ∃ (a : R) (τ' : H0 U'.LG.L k) (f' : ∀ α, D'.toPre.SecB k α), a ≠ 0 ∧ (∀ e, U'.ExpandsAt e k τ' f') ∧
      AgreeAll U.toUnifPre U'.toUnifPre hD j k (SecOps.secScale (scal G.hom a) τ) τ' ∧
      ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x)
        (SecOps.secScale (scal D.toPre.P.A.hom a) (f (hD.xe x))) := by
  obtain ⟨s, hs⟩ := exists_restrict U.toUnifPre k τ
  obtain ⟨F, ⟨r, hr, σ, f₀, h₁, h₂, h₃⟩, -⟩ := (U.expand k hk).1 s
  obtain ⟨F', hF⟩ := exists_pull hD _ hG k F
  obtain ⟨s', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (U'.expand k hk).2 F'
  have e₁ : SecOps.secScale (scal G.hom r') σ = SecOps.secScale (scal G.hom (r' * r)) τ :=
    SecOps.sec_ext (scale_of_restrict _ hs h₁ r')
  have e₂ := expansion_eq hR U.toUnifPre (fun e => e₁ ▸ expandsAt_scale _ (h₃ e) r')
    (fun e => expandsAt_scale _ (hE e) (r' * r))
  have hp := fun x => congrFun e₂ (hD.xe x) ▸ integral_rel hD _ hF h₂ h₂' x
  exact ⟨r' * r, _, _, mul_ne_zero hr' hr, fun e => expandsAt_scale _ (h₃' e) r,
    hj.agreeAll (fun e => expandsAt_scale _ (hE e) _) (fun e => expandsAt_scale _ (h₃' e) _) hp, hp⟩

end GlobalTheory.GenericIso

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull GlobalTheory.ExpGTrans GlobalTheory.GenericIso in
theorem expandsG_of_genericRel : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → ∀ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (σ : U.SecGF F k) (σ' : U'.SecGF F k) (s : Fam D.toPre F k) (s' : Fam D'.toPre F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (UnifPre.GF (G := G') F).left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ (TFK (R := R) F ◁ Φ.hom).left ≫ UnifPre.gFK (G := G) F) z ∈ U.LG.L.U jL → (r ≫ UnifPre.gFK (G := G') F) z ∈ U'.LG.L.U jL' → gs (r ≫ (TFK (R := R) F ◁ Φ.hom).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) z jL (fun _ => jL') ^ k).val * gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G') F) (fun _ => jL')) (σ'.f (fun _ => jL'))) → GlobalTheory.RigidSections.FamRel hD F s'.s s.s → U.ExpandsG F k σ s → U'.ExpandsG F k σ' s' := by
  intro hGl R _ _ I hR D D' A A' G G' _ _ _ _ _ _ U U' hD j hj Φ w hw F _ _ k hk σ σ' s s' hσ hs
    ⟨n, c, τ, f, hE, hG, hB⟩
  choose a τ' f' ha hE' hA hf using fun i => hj.exists_expansion hGl hR hk (τ i) (f i) (hE i)
  let ρ : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hρ : ∀ i, ρ (a i) ≠ 0 := fun i =>
    (map_ne_zero_iff ρ ((algebraMap (FractionRing R) F).injective.comp
      (IsFractionRing.injective R (FractionRing R)))).2 (ha i)
  have hT : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom ρ) := (spMap_comp _ _).symm
  have pG : UnifPre.gFK (G := G) F ≫ G.hom =
      (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ Spec.map (CommRingCat.ofHom ρ) := by
    have e₁ := Over.w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G))
    have e₂ := Over.w (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G))
    rw [← hT, Category.assoc, pullback.condition]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) (e₁.trans e₂.symm)).trans (Category.assoc _ _ _))
  have pB : (DegPre.prB D.toPre F).left ≫ D.toPre.P.A.hom =
      (fst (TF (R := R) F) D.toPre.P.A).left ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [Over.w, ← hT]
    exact (Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm
  refine ⟨n, fun i => c i / ρ (a i), τ', f', hE', ?_, fun x => ?_⟩
  · refine (FieldBaseChange.secLin_iff_val U'.LG.isLB _ _ _ _).2 fun y J' hJ' => ?_
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at (Z := (UnifPre.GF (G := G') F).left) U.LG.isLB y
    have a₁ : (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) ≫ Φ.hom.left ≫
        pullback.fst G.hom (jK R) = (𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ UnifPre.gFK (G := G) F := by
      have e := congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) Φ.hom)
      simp only [Over.comp_left] at e
      rw [Category.id_comp, Category.id_comp, ← Category.assoc, ← e, Category.assoc]
    have a₂ : (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) ≫ pullback.fst G'.hom (jK R) =
        𝟙 _ ≫ UnifPre.gFK (G := G') F := Category.assoc _ _ _
    have a₃ : (𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
        𝟙 _ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left :=
      (Category.assoc _ _ _).trans
        (congrArg (𝟙 _ ≫ ·) (congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) Φ.hom)))
    have e₁ := hσ _ (𝟙 _) y _ _ (hJ ((𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ UnifPre.gFK (G := G) F))
      (hJ' (𝟙 _ ≫ UnifPre.gFK (G := G') F))
    have e₃ := secLin_val (secLin_rescale U.LG.isLB ρ G.hom pG a hρ hG) (𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) y hJ
    refine (Units.mul_right_inj _).1 (e₁.symm.trans (e₃.trans ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e₂ := hw.2 k hk _ _ (hA i) _ (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left) y
      (J ((𝟙 _ ≫ (TFK (R := R) F ◁ Φ.hom).left) ≫ UnifPre.gFK (G := G) F)) (J' (𝟙 _ ≫ UnifPre.gFK (G := G') F))
      (by rw [a₁]; exact hJ _) (by rw [a₂]; exact hJ' _)
    rw [a₁, a₂] at e₂
    rw [ExpInt.gs_scal, ExpInt.gs_scal, a₃, mul_left_comm]
    refine congrArg (_ * ·) ?_
    refine (sval_of _ _ y J _ fun _ => ?_).trans (e₂.trans (congrArg (_ * ·) (sval_of _ _ y J' _ fun _ => ?_).symm))
    · rw [Category.comp_id]
    · rw [Category.comp_id]
  · refine secLin_transport D.toPre.P.isLB D'.toPre.P.isLB hD.w _ _ _ _ _ _ _ (prF hD F) _
      (famφ_eq D.toPre F (hD.xe x)) (famφ_eq D'.toPre F x) (famφB_pull hD x) (prF_snd hD F) _ _ (fun i y => ?_)
      _ _ _ _ (hs x) (fun i => hf i x) (secLin_rescale D.toPre.P.isLB ρ D.toPre.P.A.hom pB a hρ (hB (hD.xe x)))
    rw [ExpInt.gs_scal, ExpInt.gs_scal, Category.assoc, prF_fst]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmersedByOfLocalCoords
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.SecImm
open GlobalTheory.Points GlobalTheory.ProjSpace

section
variable {o : Type} [CommRing o] {m m' : ℕ} {K : Type} [Field K] {Y : Scheme.{0}}

theorem crd_toProj {L : LB Y} (f : Y ⟶ Sp o) (s : Fin (m + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (x : Sp K ⟶ Y) (k : L.ι) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    Crd (O1 o m) (coord o m) (x ≫ toProj f s hs) (fun i => valF x _ ((s i).f k)) := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top (x ≫ toProj f s hs) (iSup_chart o m)
  have hT : ⊤ ≤ x ⁻¹ᵁ (toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k) := fun z hz => ⟨hi hz, hk hz⟩
  have hu := (isUnit_resG_sec (s i) k (W := toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k)
    (inf_le_left.trans (toProj_preimage_chart f s hs i).le) inf_le_right).map (valMap x _ hT).hom
  rw [← valR_eq] at hu
  refine (LinFrame.crd_iff _ _).2 ⟨i, hu.unit, hi, fun j => ?_⟩
  have := congrArg (valR x _) (sec_eq_pullRatio_toProj_mul f s hs i j k
    (W := toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k) inf_le_left inf_le_right)
  rw [valR_mul x _ hT, valR_res x _ hT, LinFrame.valR_pullRatio x _ _ hT] at this
  exact this.trans (mul_comm _ _)

end

end GlobalTheory.ZH.SecImm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitGenericOfBasedWeightedChartsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_generic_of_based_weightedCharts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  first | exact @GlobalTheory.ZJ.Charts.split_generic_of_based | exact GlobalTheory.ZJ.Charts.split_generic_of_based | (intros; apply GlobalTheory.ZJ.Charts.split_generic_of_based <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusIsAffineHomAndSplitsFinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem torus_isAffineHom_and_splits_finite : NaSt.{0} := by
  intro k _ T _ hT
  obtain ⟨Ω, _, _, X, _, _, _, e, he⟩ := hT.splits
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    ⟨fun x => ⟨(default : Spec (.of Ω)), Subsingleton.elim (α := Spec (.of k)) _ _⟩⟩
  have haff : IsAffineHom T.hom := by
    refine isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ T.hom _ hsurj hflat inferInstance ?_
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h : IsAffineHom (e.hom.left ≫ (splitTorus (Spec (.of Ω)) X).hom) := inferInstance
    rw [Over.w] at h
    exact h
  refine ⟨haff, ?_⟩
  obtain ⟨k', _, _, _, e', he'⟩ := IsoFinite.exists_finite_iso k Ω T (splitTorus (Spec (.of k)) X)
    haff inferInstance hT.finiteType inferInstance
    ⟨e ≪≫ (Diag.baseChangeIso _ X).symm,
      inferInstanceAs (IsMonHom (e.hom ≫ (Diag.baseChangeIso _ X).inv))⟩
  exact ⟨k', inferInstance, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
    e' ≪≫ Diag.baseChangeIso _ X, inferInstanceAs (IsMonHom (e'.hom ≫ (Diag.baseChangeIso _ X).hom))⟩

end GlobalTheory
end

