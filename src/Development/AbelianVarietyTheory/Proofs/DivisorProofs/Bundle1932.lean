module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratFunc_C_laurent (F : Type) [Field F] : (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C =
    (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  ext1 a
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

theorem sqr_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : sqr G' ≫ φ = φ ≫ sqr G := by
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e := h.2 G' (𝟙 G') (𝟙 G') x₀ x₀ rfl rfl
  have e2 : x₀ * x₀ = x₀ ≫ (𝟙 G * 𝟙 G) := by rw [comp_mul]; simp
  rw [e2] at e
  exact e.symm

theorem ratRigid_of_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (Ω : Type) [Field Ω] [CharZero Ω]
    (b : Sp Ω ⟶ S), RatRigid ((Over.pullback b).obj G) (𝟙 (Sp Ω)) → RatRigid G b := by
  intro S G _ Ω _ _ b hR ξ hξ ⟨β, hβ⟩
  have hp := isGrpPullback_pullback G b
  have hu : unitSec ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = b ≫ unitSec G := unitSec_comp hp
  have hs : sqr ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = pullback.fst G.hom b ≫ sqr G :=
    sqr_comp_of_isGrpPullback hp
  have hsh : sqr ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = pullback.snd G.hom b :=
    Over.w (𝟙 ((Over.pullback b).obj G) * 𝟙 ((Over.pullback b).obj G))
  have hus : unitSec ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = 𝟙 _ := sec_hom _
  let ξ' : Sp (PowerSeries Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift ξ (spMap PowerSeries.C) hξ.base
  have hξ₁ : ξ' ≫ pullback.fst G.hom b = ξ := pullback.lift_fst _ _ _
  have hξ₂ : ξ' ≫ pullback.snd G.hom b = spMap PowerSeries.C := pullback.lift_snd _ _ _
  have hsp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hpath : IsPath ((Over.pullback b).obj G) 2 (𝟙 (Sp Ω)) ξ' := by
    refine ⟨?_, ?_, ?_⟩
    · exact hξ₂.trans (Category.comp_id _).symm
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, hξ.zero, Category.assoc, hu, Category.id_comp]
      · rw [Category.assoc, hξ₂, Category.assoc, hus, Category.id_comp, hsp]
        have : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω := by
          ext a; simp
        rw [this]
        show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = _
        rw [CommRingCat.ofHom_id, Spec.map_id]
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, Category.assoc, hs, ← Category.assoc, hξ₁, hξ.scale]
      · rw [Category.assoc, hξ₂, Category.assoc, hsh, hξ₂, hsp]
        have : (PowerSeries.rescale (2 : Ω)).comp PowerSeries.C = PowerSeries.C := by
          ext1 a; ext n; rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
          rcases n with _ | n <;> simp
        rw [this]
  have hβb : β ≫ G.hom = spMap RatFunc.C ≫ b := by
    have cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    apply cancel (algebraMap (RatFunc Ω) (LaurentSeries Ω))
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, ← Category.assoc, ← Category.assoc, hsp, hsp,
      ratFunc_C_laurent]
  let β' : Sp (RatFunc Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift β (spMap RatFunc.C) hβb
  have hrat : IsRatPath ξ' := by
    refine ⟨β', ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hξ₁, hβ]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hξ₂, hsp, hsp, ratFunc_C_laurent]
  have e := hR ξ' hpath hrat
  rw [← hξ₁, e]
  simp only [triv, Category.assoc, hu, Category.id_comp]

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdZeroOfPetAt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.PetDef

open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adelAut_of_gamma {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} (hχ : ∀ k la γ, γ ∈ (X k).Γ → (X k).χ la γ = 1) (hd : DictIsUnif V dict Kf th hr)
    (hm : MuUnit V dict mu) (hL : DictLoc V dict) (hmc : Continuous mu) : AdelAut V dict mu := by
  intro la P hP
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · obtain ⟨γ', hγ', he⟩ := hd.1 γ hγ g
    have hE := (eqv_holSub X la (holCusp_mem_holSub X la hP)).2 (dict g).1 γ' hγ' (dict g).2 (hd.2.2.2.1 g)
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hE, hχ _ _ _ hγ', one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
    have hsec : (X k).IsSec (la k) (P k) := (hP k).1.1
    have hPc : ContinuousOn (P k) (X k).dom := hsec.1.continuousOn
    have hc : ContinuousOn (fun g => mu g * P k (x g)) N :=
      hmc.continuousOn.mul (hPc.comp hx fun g hg => (hs g hg).1)
    have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      obtain ⟨hd', γ, hγ, he⟩ := hs g hg
      show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show mu g * P k (x g) = mu g * P k (lact γ (x g))
      rw [hsec.2.2 γ hγ (x g) hd', hχ _ _ _ hγ, one_mul]
    exact (hc.continuousAt hN).congr heq

end Gen

section Cover

variable {D : D7} {T : Core D} {j : ℕ}

theorem dictLoc_of_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ)
    (hσ : GoodEmb Y.d.c₂ σ) : ∃ th hr, DictIsUnif (D.sp.W j) (Y.dict σ) Y.Kf th hr ∧ DictLoc (D.sp.W j) (Y.dict σ) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  refine ⟨th, hr, hd, ?_⟩
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hK : Y.Kf ≤ GfC (D.sp.W j) := fun k hk => ((h.levelK k).1 hk).1
  exact GlobalTheory.DictLocTest.locClause_of_unif_places hd hK (_root_.GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)

theorem muUnit_one (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
  ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, h.unit σ hσ⟩

theorem adelAut_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelAut (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, hL⟩ := dictLoc_of_good Y h σ hσ
  exact adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd (muUnit_one Y h σ hσ) hL
    continuous_const

theorem aeDom_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AeDom Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, -⟩ := dictLoc_of_good Y h σ hσ
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  exact aeDom_of_aut Y.d.Xo₂ Y.d.c₂ (adelAut_good Y h σ hσ) (quotSupp_of _ hV hP) (muUnit_one Y h σ hσ) hd

end Cover

end GlobalTheory.PetDef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePoint
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKS

open MonObj

theorem IsTranslate.fst_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g₀ : Sp S ⟶ t.G.left) (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ x → IsTanAtG t x v → IsTranslate t φ g₀ v w → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ := by
  intro E _ _ _ H X t R S _ _ φ x g₀ v w hg hv ⟨g', v', h₁, h₂, h₃⟩
  have e1 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
  have e2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ) =
      spMap φ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => by simp [dualMap]
  let r : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show _ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom = g₀ ≫ t.G.hom
      rw [← Category.assoc, e1, Category.id_comp])
  let q : Over.mk (g₀ ≫ t.G.hom) ⟶ Over.mk x := Over.homMk (spMap φ) hg.symm
  have hv1 : r ≫ v' = 1 := by
    rw [← MonObj.comp_one q]
    apply Over.OverMorphism.ext
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v'.left = spMap φ ≫ _
    rw [h₂, ← Category.assoc, e2, Category.assoc, hv.2]
  have h : (r ≫ (g' * v')).left = (r ≫ g').left := by
    rw [MonObj.comp_mul, hv1, _root_.mul_one]
  rw [← h₃]
  refine h.trans ?_
  show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ g'.left = g₀
  rw [h₁, ← Category.assoc, e1, Category.id_comp]

end GlobalTheory.LogKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

def termV {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι)
    (g : GtPt D (epsR R)) {k : ℕ} {α : D.X} (f : D.SecB k α) : DualNumber R :=
  valR g.b.left (LB.wchart D.P.L (D.famφB α) fun i => J (g.b.left ≫ D.famφB α i))
      (f.f fun i => J (g.b.left ≫ D.famφB α i)) *
    valR (𝟙 (Sp (DualNumber R))) (LB.wchart D.P.L (DegPre.gtφT D (epsR R) g.b α) fun i => J (DegPre.gtφT D (epsR R) g.b α i))
      ((g.s α).s fun i => J (DegPre.gtφT D (epsR R) g.b α i)).val

def rigVal {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (j : L.L.ι) : S :=
  valR (𝟙 (Sp S)) ((L.L.pull (eSec G)).U fun _ => j) (L.rig.s fun _ => j).val

def rigValD {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (j : D.P.L.ι) : R :=
  valR (𝟙 (Sp R)) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) fun _ => j) (D.rig.s fun _ => j).val

end GlobalTheory.MBLow.TanExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodWeightDictionary
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.GoodWCore

theorem fullLat_congr {K Rg : Type} [Field K] [NumberField K] [CommRing Rg] [Algebra K Rg] [Algebra (𝓞 K) Rg]
    [IsScalarTower (𝓞 K) K Rg] {C C' : Submodule K Rg} (h : C = C')
    {Vs : HeightOneSpectrum (𝓞 K) → Set (Rg → EReal)} {hV : ∀ la, ∀ v ∈ Vs la, IsVal la v}
    (hl : FullLat C Vs hV) : FullLat C' Vs hV := by
  subst h
  exact hl


set_option maxHeartbeats 8000000 in
theorem goodW_core {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j)
    (hl : Submodule.IsFullLattice T.Q.c.F (supLat (T.cuspA j (wtA w) w.n))) :
    GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ (wtA w) w.n) := by
  have hlat : Submodule.IsFullLattice T.Q.c.F (AllWt.latW (T.U j) (wtZ (wtA w) w.n)) := by
    rw [AllWt.latW, cuspW_wtZ]
    exact hl
  have hspan := Submodule.IsFullLattice.span_eq_top (self := hlat)
  refine ⟨?_, hlat.fg, hspan⟩
  have : FiniteDimensional T.Q.c.F (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n)) := by
    obtain ⟨s, hs⟩ := hlat.fg
    refine ⟨⟨s, ?_⟩⟩
    rw [← hspan, ← hs, Submodule.span_span_of_tower]
  refine GlobalTheory.HSApp.hasGram_of_inner _ _ _ fun v => ?_
  set σ := goodOf T.Q.c v.embedding with hσdef
  have hσ : GoodEmb T.Q.c σ := goodEmb_goodOf _ _
  have hD : Dom (wtA w) w.n := dom_wtA w
  let ι := LinearEquiv.ofEq _ _ (cuspW_wtZ (Xo := T.Q.Xo j) (c := T.Q.c) (U := T.U j) (wtA w) w.n)
  let cf : ℝ := lieFac (T.Q.Dw j) (xiR D) (wtA w)
  have hcf : 0 < cf := lieFac_pos _ _ _
  let J := uniformisationL2 (T.V j σ) σ (rdC (T.U j) σ (wtA w) w.n) (T.dict j σ) (T.mu j σ)
    (hT.cuspidalL2Subspace j hj σ hσ (wtA w) w.n hD)
  let Φ : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ (wtA w) w.n) →+ MeasureTheory.Lp ℂ 2 (muQ1 (T.V j σ)) :=
    AddMonoidHom.mk' (fun f => (cf : ℂ) • J (ι f)) (fun f g => by rw [map_add (f := _), map_add (f := _), smul_add])
  have hΦ : ∀ f, Φ f = (cf : ℂ) • J (ι f) := fun _ => rfl
  have hs : ∀ (a : T.Q.c.F) f, Φ (a • f) = σ a • Φ f := fun a f => by
    rw [hΦ, hΦ, map_smul, map_smulₛₗ]
    exact smul_comm _ _ _
  refine ⟨_, inferInstance, inferInstance, Φ, ?_, ?_, ?_⟩
  · by_cases hg : GoodEmb T.Q.c v.embedding
    · left
      intro a f
      have e' : σ a = v.embedding a := by
        rw [hσdef]; unfold goodOf; rw [ite_eq_left hg]
      rw [hs, e']
    · right
      intro a f
      have e' : σ a = starRingEnd ℂ (v.embedding a) := by
        rw [hσdef]; unfold goodOf; rw [ite_eq_right hg]; rfl
      rw [hs, e']
  · intro f
    have hf : (f : Rul (T.Q.Xo j) T.Q.c) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := (ι f).2
    have e1 : normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ (wtA w) w.n) v.embedding f =
        petAt (T.U j σ) (xiR D) (T.V j σ) (T.dict j σ) (muQ1 (T.V j σ)) (wtZ (wtA w) w.n) f := rfl
    rw [e1, petAt_wtZ (T.U j) (xiR D) (T.V j σ) (T.dict j σ) (T.mu j σ) (hT.muUnit j hj σ hσ) _ _
      (hT.cuspidalL2Subspace j hj σ hσ (wtA w) w.n hD) hf, l2C, dite_eq_left hf, hΦ, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hcf.le]
    rfl
  · intro m e he
    have hi : LinearIndependent T.Q.c.F fun k => ι (e k) := he.map' ι.toLinearMap ι.ker
    have h1 := (GlobalTheory.VolPairExists.adelic_linearIndependent D T hT j hj σ hσ (wtA w) w.n hD).2 m _ hi
    rw [Fintype.linearIndependent_iff] at h1 ⊢
    intro c hc
    refine h1 c ?_
    have : (cf : ℂ) • ∑ k, c k • J (ι (e k)) = 0 := by
      rw [Finset.smul_sum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hc
      rw [hΦ]
      exact smul_comm _ _ _
    exact (smul_eq_zero.1 this).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')

end GlobalTheory.CovTop.GoodWCore

namespace GlobalTheory.CovTop

end GlobalTheory.CovTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLatticeFinitelyGenerated
section
set_option synthInstance.maxHeartbeats 400000
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.LatAllFG

theorem fg_latOf_congr {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] {C C' : Submodule K R} (hC : C = C')
    (Vs : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (h : (latOf C Vs hV).FG) : (latOf C' Vs hV).FG := by
  subst hC; exact h

theorem latW_fg {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) :
    (latW (T.U j) (wtZ (wtA w) w.n)).FG := by
  have h := (GlobalTheory.SupFull.fullAt_of_pins D T.toCore hT.pins j hj (hT.unf j hj _ T.good_σ₀) w hn).1
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.supLat GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.latIn at h
  have h2 := Submodule.fg_of_fg_map_injective _ Subtype.val_injective h
  exact fg_latOf_congr (cuspW_wtZ (Xo := T.Q.Xo j) (c := T.Q.c) (U := T.U j) (wtA w) w.n).symm _ _ h2

theorem fg_span_image {K L V W : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module L W] [Module (𝓞 L) W] [IsScalarTower (𝓞 L) L W]
    (ι : V →ₛₗ[algebraMap K L] W) (M : Submodule (𝓞 K) V) (hM : M.FG) :
    (Submodule.span (𝓞 L) (ι '' (M : Set V))).FG := by
  classical
  obtain ⟨s, hs⟩ := hM
  refine ⟨s.image ι, le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image]
    exact Submodule.span_mono (Set.image_mono (hs ▸ Submodule.subset_span))
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have e : ι (c • y) = (RingOfIntegers.mapRingHom (algebraMap K L) c) • ι y := by
        rw [← algebraMap_smul K c y, ι.map_smulₛₗ, ← algebraMap_smul L (RingOfIntegers.mapRingHom (algebraMap K L) c) (ι y)]
        rfl
      rw [e]
      exact Submodule.smul_mem _ _ hy

end GlobalTheory.CovTop.LatAllFG

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowNormHasGram
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.GramPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem embedding_eq_or {K : Type} [Field K] (σ₀ : K →+* ℂ) (v : InfinitePlace K) :
    (∀ a, sgAt σ₀ v a = v.embedding a) ∨ ∀ a, sgAt σ₀ v a = starRingEnd ℂ (v.embedding a) := by
  by_cases hv : v = InfinitePlace.mk σ₀
  · rw [sgAt_mk σ₀ hv]
    rcases InfinitePlace.embedding_mk_eq σ₀ with h | h
    · exact Or.inl fun a => by rw [hv, h]
    · exact Or.inr fun a => by rw [hv, h]; simp
  · exact Or.inl fun a => by simp [sgAt, hv]

theorem hasGram_of_unif {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hU : R.LUnif) (i : Fin D.R.m) :
    HasGram (nrmR R i) := by
  refine GlobalTheory.HSApp.hasGram_of_inner _ _ _ fun v => ?_
  refine ⟨(R.HW i (sgAt D.what₂.embLL v)).H, inferInstance, inferInstance,
    ((R.FW i).j (sgAt D.what₂.embLL v)).toAddMonoidHom, ?_, fun x => ?_, fun n e he => (hU i _).1 n e he⟩
  · refine (embedding_eq_or D.what₂.embLL v).imp (fun h a x => ?_) fun h a x => ?_
    · rw [← h]; exact map_smulₛₗ ((R.FW i).j (sgAt D.what₂.embLL v)) a x
    · rw [← h]; exact map_smulₛₗ ((R.FW i).j (sgAt D.what₂.embLL v)) a x
  · unfold nrmR
    rw [InfinitePlace.mk_embedding]
    rfl

end GlobalTheory.CovTop.GramPt

end
end

