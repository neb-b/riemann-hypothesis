module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUnique
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isMapOf_existsUnique_and : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ f : G ⟶ H, (∃! φ, c.IsMapOf c' f φ) ∧ ∀ (φ : Fin e → MvPowerSeries (Fin d) k), c.IsMapOf c' f φ → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n, (∀ g, c.ev n (subst φ g) = f.app n (c'.ev n g)) ∧ ∀ s, c.ev₂ n (pull2 φ s) = pullbackTwo (f.app n) (c'.ev₂ n s) := by
  intro p k _ d e G H c c' f
  have hone := (_root_.GlobalTheory.Katz.Chart.functions_are_series p k d G c).2.2
  have hcomp : ∀ j n, G.res n (f.app (n + 1) (c'.x (n + 1) j)) = f.app n (c'.x n j) := fun j n => by
    rw [res_app, c'.res]
  refine ⟨?_, ?_⟩
  · choose φ hφ _ using fun j => hone (fun n => f.app n (c'.x n j)) (hcomp j)
    refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => ?_⟩
    obtain ⟨g, -, hg⟩ := hone (fun n => f.app n (c'.x n j)) (hcomp j)
    exact (hg (ψ j) fun n => hψ n j).trans (hg (φ j) fun n => hφ j n).symm
  intro φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d (G.A 0) (c.x 0) (c.nil 0) (c.aug 0) (φ j)).1
    change Coalgebra.counit (R := k) (c.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, CoalgHomClass.counit_comp_apply, c'.aug]
  refine ⟨hconst, fun n => ⟨fun g => ?_, fun s => ?_⟩⟩
  · have hy : ∀ j, IsNilpotent (f.app n (c'.x n j)) := fun j => (c'.nil n j).map (f.app n)
    have h1 := (_root_.GlobalTheory.evA_subst_and_map k (Fin e) (G.A n)).1 (Fin d) (c.ev n)
      (fun t => by
        change IsNilpotent (evA k (c.x n) (c.nil n) (X t))
        rw [evA_X]; exact c.nil n t) φ hconst _ hy (fun j => hφ n j) g
    rw [h1]
    exact ((_root_.GlobalTheory.evA_subst_and_map k (Fin e) (H.A n)).2 (G.A n) (f.app n : H.A n →ₐ[k] G.A n) (c'.x n)
      (c'.nil n) _ hy (fun _ => rfl) g).symm
  · let F : H.A n ⊗[k] H.A n →ₐ[k] G.A n ⊗[k] G.A n :=
      Algebra.TensorProduct.map (f.app n : H.A n →ₐ[k] G.A n) (f.app n : H.A n →ₐ[k] G.A n)
    have hy : ∀ i, IsNilpotent (F (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map F
    have hev := _root_.GlobalTheory.EvSquare.main p k d G c n
    have ha : ∀ i, constantCoeff ((Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) :
        Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k) i) = 0 := by
      intro i
      have hc := hev.2.2.2
      cases i with
      | inl j =>
        rw [Sum.elim_inl, ← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
      | inr j =>
        rw [Sum.elim_inr, ← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
    have h1 := (_root_.GlobalTheory.evA_subst_and_map k (Fin e ⊕ Fin e) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n)
      (fun t => by
        change IsNilpotent (evA k (c.x₂ n) (c.nil₂ n) (X t))
        rw [evA_X]; exact c.nil₂ n t) _ ha _ hy
      (fun i => by
        cases i with
        | inl j =>
          simp only [Sum.elim_inl]
          rw [hev.1, hφ n j]
          show _ = F (c'.x n j ⊗ₜ 1)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
        | inr j =>
          simp only [Sum.elim_inr]
          rw [hev.2.1, hφ n j]
          show _ = F (1 ⊗ₜ c'.x n j)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl) s
    have h2 := (_root_.GlobalTheory.evA_subst_and_map k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n ⊗[k] G.A n) F
      (c'.x₂ n) (c'.nil₂ n) _ hy (fun _ => rfl) s
    have h3 : pullbackTwo (f.app n) (c'.ev₂ n s) = F (c'.ev₂ n s) := by
      induction (c'.ev₂ n s) with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b => rfl
    unfold pull2 at2
    rw [h1, h3]
    exact h2.symm

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossRelationHomGivesExpansionTermConvolutionRel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.Mum.MixTwo

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

abbrev homF (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (UnifPre.GF (G := G₁) F).left ⟶ (UnifPre.GF (G := G₂) F).left :=
  (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left

theorem homF_str (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    homF a F ≫ MixedConv.strF G₂ F = MixedConv.strF G₁ F :=
  congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) ((Over.pullback (jK R)).map a))

theorem homF_gFK (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    homF a F ≫ UnifPre.gFK (G := G₂) F = UnifPre.gFK (G := G₁) F ≫ a.left := by
  have h₁ := congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) ((Over.pullback (jK R)).map a))
  have h₂ : ((Over.pullback (jK R)).map a).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ a.left :=
    pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G₂.hom (jK R)) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

theorem val_secLin' {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {U : UnifPre I D A G} {F : Type} [Field F] [Algebra (FractionRing R) F] {k n : ℕ} {σ₀ : U.SecGF F k}
    {σ : Fin n → H0 U.LG.L k} {c : Fin n → F}
    (h : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) σ₀
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)))
    {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of F)) (r : Y ⟶ (UnifPre.GF (G := G) F).left)
    (hr : r ≫ MixedConv.strF G F = q) (y : Y) {J} (hJ : Good U.LG.L y J) :
    sval σ₀ r y J = ∑ i, GlobalTheory.BoxExpansion.constHomVal q y (c i) *
      sval (σ i) (r ≫ UnifPre.gFK (G := G) F) y J :=
  (GlobalTheory.BoxExpansion.secLin_val h r y hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _)
    ((gs_scal (MixedConv.strF G F) r y _).trans ((congrArg (fun q => constVal q y (c i)) hr).trans
      (GlobalTheory.BoxExpansion.constVal_eq _ _ _))))

theorem coreF₂ [CharZero R] (hL : LL) (hR : AdmBase R I) {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}
    {a : G₁ ⟶ G₂} {b : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {h : D₂.toPre.X →+ D₁.toPre.X} (hLin : Lin U₁ U₂ a b h)
    (hCo : Coord U₁ U₂ a b h) {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (j j' : ℕ)
    {N : Type} [Fintype N] (c : N → F) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j')
    (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α)
    (hE : ∀ ν e, U₂.ExpandsAt e j (σ ν) (f ν)) (hE' : ∀ ν e, U₁.ExpandsAt e j' (σ' ν) (f' ν))
    (hrel : ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ →
      ∑ ν, GlobalTheory.BoxExpansion.constHomVal (MixedConv.strF G₁ F) y (c ν) *
        (sval (σ ν) (UnifPre.gFK (G := G₁) F ≫ a.left) y J₂ * sval (σ' ν) (UnifPre.gFK (G := G₁) F) y J₁) = 0)
    (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F) (hg : Act D₁.toPre D₂.toPre b h g g')
    (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b) (hw : w.IsGen) (hw' : w'.IsGen)
    (x : N → D₂.toPre.X → F) (x' : N → D₁.toPre.X → F)
    (hx : ∀ ν χ, MixedConv.IsCoefB j g' w χ (f ν χ) (x ν χ)) (hx' : ∀ ν χ, MixedConv.IsCoefB j' g w' χ (f' ν χ) (x' ν χ))
    (α : D₁.toPre.X) :
    SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} =>
      ∑ ν, c ν * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  obtain ⟨n, β, ρ, hβ, hc⟩ := MixedConv.exists_indep (R := R) c
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  have P₁ := isPart_inl U₁.LG.L U₂.LG.L
  have P₂ := isPart_inr U₁.LG.L U₂.LG.L
  let d : Fin n → SecOver G₁.hom (LB.LinComb (join U₁.LG.L U₂.LG.L)
      (Sum.elim (fun _ : Fin 1 => (a.left ≫ 𝟙 G₂.left) ≫ coprod.inr) (fun _ : Fin 1 => 𝟙 G₁.left ≫ coprod.inl))
      (Sum.elim (fun _ => (j : ℤ)) (fun _ => (j' : ℤ)))) := fun m =>
    ∑ ν, ρ m ν • (show SecOver G₁.hom _ from
      H1.SectionArithmetic.mulSec (P₂.sec (H1.SectionArithmetic.pullSec (σ ν) a.left)) (P₁.sec (σ' ν)))
  have hd : ∀ m (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J), Good (join U₁.LG.L U₂.LG.L) z J →
      sval (d m) r z J = ∑ ν, constVal (r ≫ G₁.hom) z (ρ m ν) *
        (sval (σ ν) (r ≫ a.left) z (rr J) * sval (σ' ν) r z (rl J)) :=
    fun m Z r z J hJ => (sval_sum' (π := G₁.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
      (sval_smul' (π := G₁.hom) hJ _ _ _).trans (congrArg _ ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans
        (congrArg₂ (· * ·) ((P₂.sval_sec _ r z hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z (P₂.good hJ)))
          (P₁.sval_sec _ r z hJ)))))
  have := U₁.smooth
  have h₀ := _root_.GlobalTheory.sval_eq_zero_of_indep_comb R F _ _ _ _ G₁.hom (MixedConv.strF G₁ F) _ MixedConv.isPullback_GF
    (join U₁.LG.L U₂.LG.L) (join_isLB U₁.LG.isLB U₂.LG.isLB) _ _ _ _ β hβ d
    (fun y J hJ => by
      refine Eq.trans ?_ (hrel y (rl J) (rr J) (P₁.good hJ) (P₂.good hJ))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hd _ _ _ y J hJ, hc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => ?_
      rw [(MixedConv.isPullback_GF (G := G₁) (F := F)).w, constVal_specMap, GlobalTheory.BoxExpansion.constVal_eq,
        GlobalTheory.BoxExpansion.constVal_eq, _root_.mul_assoc]
      rfl)
  have h₁ := MixedConv.sumF_comb hR Finset.univ β _ fun m => _root_.GlobalTheory.Mum.Two.Mix.core hL R I hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a b h hLin hCo F
    j j' N (ρ m) σ σ' f f' hE hE' (fun Z r z J₁ J₂ hJ₁ hJ₂ => by
      obtain ⟨J, hJ, rfl, rfl⟩ := exists_good_join U₁.LG.isLB U₂.LG.isLB hJ₁ hJ₂
      exact (hd m Z r z J hJ).symm.trans (h₀ m Z r z J hJ)) g g' hg w w' hw hw' x x' hx hx' α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp h₁
  simp only [hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => (_root_.mul_assoc _ _ _).symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₁ : W0 U₁.toUnifPre) (w₂ : W0 U₂.toUnifPre), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') s₁ s₂ s₁' s₂', U₂.ExpandsF F j w₂ t₁ s₁ → U₂.ExpandsF F j w₂ t₂ s₂ → U₁.ExpandsF F j' w₁ t₁' s₁' → U₁.ExpandsF F j' w₁ t₂' s₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  intro R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ _ _ U₁ U₂ a c b h _ hG hLin hCo F _ _ _ w₁ w₂ hw₁ hw₂ j j' _ _
    t₁ t₂ t₁' t₂' s₁ s₂ s₁' s₂' H₁ H₂ H₁' H₂' hC g g' hg w w' hw hw' α
  obtain ⟨τ₁, r₁, n₁, c₁, σ₁, f₁, e₁, l₁, b₁⟩ := H₁
  obtain ⟨τ₂, r₂, n₂, c₂, σ₂, f₂, e₂, l₂, b₂⟩ := H₂
  obtain ⟨τ₁', r₁', n₁', c₁', σ₁', f₁', e₁', l₁', b₁'⟩ := H₁'
  obtain ⟨τ₂', r₂', n₂', c₂', σ₂', f₂', e₂', l₂', b₂'⟩ := H₂'
  choose x₁ hx₁ using fun i χ => MixedConv.exists_isCoefB g' hw χ (f₁ i χ)
  choose x₂ hx₂ using fun i χ => MixedConv.exists_isCoefB g' hw χ (f₂ i χ)
  choose x₁' hx₁' using fun i χ => MixedConv.exists_isCoefB g hw' χ (f₁' i χ)
  choose x₂' hx₂' using fun i χ => MixedConv.exists_isCoefB g hw' χ (f₂' i χ)
  have key := coreF₂ GlobalTheory.firstFiveLaws hR hLin hCo j j' (N := (Fin n₁ × Fin n₂') ⊕ (Fin n₂ × Fin n₁'))
    (Sum.elim (fun p => c₁ p.1 * c₂' p.2) (fun p => -(c₂ p.1 * c₁' p.2)))
    (Sum.elim (fun p => σ₁ p.1) (fun p => σ₂ p.1)) (Sum.elim (fun p => σ₂' p.2) (fun p => σ₁' p.2))
    (Sum.elim (fun p => f₁ p.1) (fun p => f₂ p.1)) (Sum.elim (fun p => f₂' p.2) (fun p => f₁' p.2))
    (by rintro (p | p); exacts [e₁ p.1, e₂ p.1]) (by rintro (p | p); exacts [e₂' p.2, e₁' p.2])
    (fun y J₁ J₂ hJ₁ hJ₂ => by
      have hh := GlobalTheory.T.carriedSections_crossRelation_of_hom R I D₁ D₂ A₁ A₂ G₁ G₂ U₁.toUnifPre U₂.toUnifPre a c hG F w₁ w₂ hw₁ hw₂ j j'
        t₁ t₂ t₁' t₂' τ₁ τ₂ τ₁' τ₂' r₁ r₂ r₁' r₂' hC y J₁ J₂ hJ₁ hJ₂
      rw [val_secLin' l₁ _ _ (homF_str a F) y hJ₂, val_secLin' l₂ _ _ (homF_str a F) y hJ₂,
        val_secLin' l₁' _ _ (Category.id_comp _) y hJ₁, val_secLin' l₂' _ _ (Category.id_comp _) y hJ₁, homF_gFK,
        Category.id_comp, Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_eq_zero] at hh
      refine Eq.trans ?_ hh
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, map_neg, map_mul,
        neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
      exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
        (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _))
    g g' hg w w' hw hw' (Sum.elim (fun p => x₁ p.1) (fun p => x₂ p.1))
    (Sum.elim (fun p => x₂' p.2) (fun p => x₁' p.2))
    (by rintro (p | p); exacts [hx₁ p.1, hx₂ p.1]) (by rintro (p | p); exacts [hx₂' p.2, hx₁' p.2]) α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp key
  rw [MixedConv.coef_of_secLin (b₁ _) (fun i => hx₁ i _), MixedConv.coef_of_secLin (b₂ _) (fun i => hx₂ i _),
    MixedConv.coef_of_secLin (b₁' _) (fun i => hx₁' i _), MixedConv.coef_of_secLin (b₂' _) (fun i => hx₂' i _),
    Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
    (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)

end GlobalTheory.Mum.MixTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamRelationNaturalSmoothLiftMorphism
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.LiftNat


set_option maxHeartbeats 2000000 in
theorem main : (∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel1 c h → Λ'.Rel1 (m.pull1 c) h' → IsPull1 hφ h h') ∧ ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel2 c h → Λ'.Rel2 (m.pull2 c) h' → IsPull2 hφ h h' := by
  refine ⟨?_, ?_⟩
  · intro D D' Λ Λ' σ φ φ₀ hφ m hi c h h' ⟨k, f, w, hc, hh, hk, hw⟩ ⟨k', f', w', hc', hh', hk', hw'⟩
    subst hh hh'
    obtain ⟨g0, hg0⟩ := _root_.GlobalTheory.PDForm.compatibleForms_cocycles_differ_by_coboundary _ _ _ _ _ _ _ _ _ _ _ _ m k k' f f' hk hk' (by rw [hc', ← hc])
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs D D' Λ Λ' σ φ φ₀ hφ m hi
    have e1 : (morMap m).h1 (QuotientAddGroup.mk k) = QuotientAddGroup.mk k' := by
      change (QuotientAddGroup.mk ((morMap m).z1 k) : (KK D'.κ D'.t).H1) = QuotientAddGroup.mk k'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨-g0, ?_⟩
      rw [map_neg, hg0]
      change -((morMap m).p1 k.1 - k'.1) = -((morMap m).p1 k.1) + k'.1
      abel
    have e2 : ((pairB Λ' φ m).pre θ).h1 (QuotientAddGroup.mk k) =
        ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).h1 (QuotientAddGroup.mk k') := by
      rw [(GlobalTheory.CxCoh.joinedOne_inst.2.1 _ _ θ (CxMap.joined_pre _ θ)).2, pairB, CxMap.cohomOne_pullback_comp, e1]
    change (QuotientAddGroup.mk (((pairB Λ' φ m).pre θ).z1 k) : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).H1) =
      QuotientAddGroup.mk (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).z1 k') at e2
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e2
    obtain ⟨g, hg⟩ := e2
    refine _root_.GlobalTheory.PDForm.isPull1_of_pair_coboundary D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' (-g) ?_
    rw [map_neg, hg]
    change -(-(((pairB Λ' φ m).pre θ).p1 k.1) + ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1) = _
    abel
  · intro D D' Λ Λ' σ φ φ₀ hφ m hi c h h' hr hr'
    obtain ⟨k, f, w, hc, hh, hk, hw⟩ := hr
    obtain ⟨k', f', w', hc', hh', hk', hw'⟩ := hr'
    subst hh hh'
    obtain ⟨g0, hg0⟩ := _root_.GlobalTheory.PDForm.ClsTwo.cob_of_class_eq _ _ _ _ _ _ _ _ _ _ _ _ m k k' f f' hk hk' (by rw [hc', ← hc])
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs D D' Λ Λ' σ φ φ₀ hφ m hi
    have e1 : (morMap m).h2 (QuotientAddGroup.mk k) = QuotientAddGroup.mk k' := by
      change (QuotientAddGroup.mk ((morMap m).z2 k) : (KK D'.κ D'.t).H2) = QuotientAddGroup.mk k'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨-g0, ?_⟩
      rw [map_neg, hg0]
      change -((morMap m).p2 k.1 - k'.1) = -((morMap m).p2 k.1) + k'.1
      abel
    have e2 : ((pairB Λ' φ m).pre θ).h2 (QuotientAddGroup.mk k) =
        ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).h2 (QuotientAddGroup.mk k') := by
      have j := GlobalTheory.CxCoh.JoinedTwoProof.main ((pairB Λ' φ m).pre θ) (pairB Λ' φ m) θ (CxMap.joined_pre _ θ)
        (QuotientAddGroup.mk k)
      refine j.trans ?_
      have j2 := CxMap.cohomTwo_pullback_comp (morMap m) ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)) (QuotientAddGroup.mk k)
      refine j2.trans ?_
      exact congrArg _ e1
    change (QuotientAddGroup.mk (((pairB Λ' φ m).pre θ).z2 k) : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).H2) =
      QuotientAddGroup.mk (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).z2 k') at e2
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e2
    obtain ⟨g, hg⟩ := e2
    refine GlobalTheory.T.deRham_degree_two_class_pullback_of_coboundary D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' (-g) ?_
    rw [map_neg, hg]
    change -(-(((pairB Λ' φ m).pre θ).p2 k.1) + ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) = _
    abel

end GlobalTheory.PDForm.LiftNat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionIsForm
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.PairForm

section Point

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem powAt_congr {G G₁ : V n → Matrix r r ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G₁) (k : ℕ) :
    powAt G v k = powAt G₁ v k := by
  simp only [powAt, curvEv, curvPoly, curv_congr h]

theorem transAt_congr {G G₁ G' G₁' : V n → Matrix r r ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G₁)
    (h' : G' =ᶠ[𝓝 v] G₁') (k : ℕ) : transAt G G' v k = transAt G₁ G₁' v k := by
  simp only [transAt, curvEv, curvPoly, curv_congr h, curv_congr h', conn_congr h, conn_congr h']

end Point

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {r : Type} [Fintype r] [DecidableEq r]

theorem contDiffAt_change (x x' : A.Pt) (h : x.pt = x'.pt) : ContDiffAt ℂ 2 (x'.ch ∘ x.ch.symm) x.crd := by
  have hs : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hm : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source := by
    refine ⟨x.ch.map_source x.2, ?_⟩
    show x.ch.symm ((x.ch) x.pt) ∈ x'.ch.source
    rw [x.ch.left_inv x.2]
    exact (congrArg (fun y => y ∈ x'.ch.source) h).mpr x'.2
  exact GlobalTheory.SCV.contDiffAt_of_differentiableOn (A.holo x.1.1 x'.1.1) (hs.mem_nhds hm) 2

theorem change_crd (x x' : A.Pt) (h : x.pt = x'.pt) : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
  show (x'.ch) (x.ch.symm ((x.ch) x.pt)) = (x'.ch) x'.pt
  rw [x.ch.left_inv x.2]
  exact congrArg x'.ch h

theorem germ_change (G : M → M → Matrix r r ℂ) (x x' : A.Pt) (h : x.pt = x'.pt) :
    (fun u => G x.pt (x.ch.symm u)) =ᶠ[𝓝 x.crd] fun u => G x'.pt (x'.ch.symm ((x'.ch ∘ x.ch.symm) u)) := by
  have hc : ContinuousAt x.ch.symm x.crd := x.ch.continuousAt_symm (x.ch.map_source x.2)
  have hmem : x'.ch.source ∈ 𝓝 (x.ch.symm x.crd) := by
    show x'.ch.source ∈ 𝓝 (x.ch.symm ((x.ch) x.pt))
    rw [x.ch.left_inv x.2]
    exact (congrArg (fun y => x'.ch.source ∈ 𝓝 y) h).mpr (x'.ch.open_source.mem_nhds x'.2)
  filter_upwards [hc hmem] with u hu
  show G x.pt (x.ch.symm u) = G x'.pt (x'.ch.symm ((x'.ch) (x.ch.symm u)))
  rw [x'.ch.left_inv hu]
  exact congrArg (fun y => G y (x.ch.symm u)) h

theorem smooth_crd (G : M → M → Matrix r r ℂ) (hG : ∀ y, SmoothUnitAt A (G y) y) (x : A.Pt) :
    MContDiffAt ∞ (fun u => G x.pt (x.ch.symm u)) x.crd ∧ IsUnit (G x.pt (x.ch.symm x.crd)).det := by
  refine ⟨((hG x.pt).2 x.1.1 x.2).self_of_nhds, ?_⟩
  show IsUnit (G x.pt (x.ch.symm ((x.ch) x.pt))).det
  rw [x.ch.left_inv x.2]
  exact (hG x.pt).1

theorem smooth_change (G : M → M → Matrix r r ℂ) (hG : ∀ y, SmoothUnitAt A (G y) y) (x x' : A.Pt) (h : x.pt = x'.pt) :
    MContDiffAt ∞ (fun u => G x'.pt (x'.ch.symm u)) ((x'.ch ∘ x.ch.symm) x.crd) ∧
      IsUnit (G x'.pt (x'.ch.symm ((x'.ch ∘ x.ch.symm) x.crd))).det := by
  rw [change_crd A x x' h]
  exact smooth_crd A G hG x'

end Manifold

theorem isForm_pow_trans : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' →
      ∀ k, A.IsForm (fld A (powFld A G k)) ∧ A.IsForm (transFld A G G' k) := by
  intro M _ n A r _ _ G G' hG k
  have sG : ∀ y, SmoothUnitAt A (G y) y := fun y => (hG.smooth y).1
  have sG' : ∀ y, SmoothUnitAt A (G' y) y := fun y => (hG.smooth y).2
  have near := _root_.GlobalTheory.ChernCalc.loc_fields_near M n A r G G' hG
  constructor
  · refine ⟨fun i S => ?_, fun x x' h => ?_⟩
    · intro v hv
      let x : A.Pt := ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩
      have hx : x.crd = v := (A.e i).right_inv hv
      obtain ⟨h1, h2⟩ := smooth_crd A G sG x
      have hs := (_root_.GlobalTheory.ChernCalc.powAt_transAt_smooth n r _ _ x.crd h1 h2 h1 h2 k).1 S
      have key : ContDiffAt ℝ ∞ (fun v => (bas n).repr (A.loc (fld A (powFld A G k)) i v) S) x.crd :=
        hs.congr_of_eventuallyEq ((near x k).mono fun u hu => congrArg (fun a => (bas n).repr a S) hu.1)
      rw [hx] at key
      exact key.contDiffWithinAt
    · obtain ⟨h1, h2⟩ := smooth_change A G sG x x' h
      have hc := ((_root_.GlobalTheory.ChernCalc.curv_pow_chern_comp_holo n n r _ (x'.ch ∘ x.ch.symm) x.crd (contDiffAt_change A x x' h) h1 h2).2 k).1
      show (powAt (fun v => G x.pt (x.ch.symm v)) x.crd k : Alt n) =
        pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (powAt (fun v => G x'.pt (x'.ch.symm v)) x'.crd k : Alt n)
      rw [powAt_congr (germ_change A G x x' h), hc, change_crd A x x' h]
  · refine ⟨fun i S => ?_, fun x x' h => ?_⟩
    · intro v hv
      let x : A.Pt := ⟨(i, (A.e i).symm v), (A.e i).map_target hv⟩
      have hx : x.crd = v := (A.e i).right_inv hv
      obtain ⟨h1, h2⟩ := smooth_crd A G sG x
      obtain ⟨h1', h2'⟩ := smooth_crd A G' sG' x
      have hs := (_root_.GlobalTheory.ChernCalc.powAt_transAt_smooth n r _ _ x.crd h1 h2 h1' h2' k).2.2 S
      have key : ContDiffAt ℝ ∞ (fun v => (bas n).repr (A.loc (transFld A G G' k) i v) S) x.crd :=
        hs.congr_of_eventuallyEq ((near x k).mono fun u hu => congrArg (fun a => (bas n).repr a S) hu.2.2)
      rw [hx] at key
      exact key.contDiffWithinAt
    · obtain ⟨h1, h2⟩ := smooth_change A G sG x x' h
      obtain ⟨h1', h2'⟩ := smooth_change A G' sG' x x' h
      have hc := _root_.GlobalTheory.ChernCalc.transAt_comp_holo n n r _ _ (x'.ch ∘ x.ch.symm) x.crd (contDiffAt_change A x x' h) h1 h2 h1' h2' k
      show transAt (fun v => G x.pt (x.ch.symm v)) (fun v => G' x.pt (x.ch.symm v)) x.crd k =
        pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd)
          (transAt (fun v => G x'.pt (x'.ch.symm v)) (fun v => G' x'.pt (x'.ch.symm v)) x'.crd k)
      rw [transAt_congr (germ_change A G x x' h) (germ_change A G' x x' h), hc, change_crd A x x' h]

end GlobalTheory.ChernCalc.PairForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeSlopeLowerBoundDefiniteCase
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

set_option synthInstance.maxHeartbeats 400000 in
theorem eigLat_slope_definite : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : Type) [Group G] [Finite G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Finite (Comp Xo c) → Nonempty (Comp Xo c) → (∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom) → ActLev (Xo := Xo) c lev → FreePt Xo c lev → Dom a n → GoodW U ξ V dict (wtZ a n) → FlatExistsAt U ξ c₁ → eigLat U lev χ (wtZ a n) ≠ ⊥ ∧ defBound Dw a n c₁ ≤ slope_sq (normW U ξ V dict (wtZ a n)) (eigLat U lev χ (wtZ a n)) / 2 := by
  intro D H Dw l Xo c r U ξ V dict G _ _ lev χ a n c₁ hD hF hN hdom hA hfree hDom hW hflat
  exact GlobalTheory.T.levelMove_eigenlattice_slope_definite D H Dw l Xo c r U ξ V dict G lev χ a n (defBound Dw a n c₁) hD hF hN hdom hA hfree hDom hW
    (_root_.GlobalTheory.DefFibre.fibreAt_defCase D.host.E H Dw l Xo c r U ξ a n c₁ hD hDom hflat)

end GlobalTheory.DefPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPsiOrdersProjectionLatticeCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_psiOrders_projectionLatticeCoordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  first | exact @GlobalTheory.Poinc.E8Lattice.main | exact GlobalTheory.Poinc.E8Lattice.main | (intros; apply GlobalTheory.Poinc.E8Lattice.main <;> assumption)
end

