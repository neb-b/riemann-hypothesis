module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsPullbackLeMulTwistDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Cartier.PullCount

open GlobalTheory.Cartier.DomPull GlobalTheory.Cartier.CartierDiv

section Pull

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]

theorem fnOf_pull_g (L : LB X) (J J' : (L.pull φ).ι)
    (hg : genericPoint X' ∈ (L.pull φ).U J ⊓ (L.pull φ).U J') :
    fnOf _ hg ((L.pull φ).g J J' : Γ(X', (L.pull φ).U J ⊓ (L.pull φ).U J')) =
      GlobalTheory.functionFieldMap φ (fnOf _ (gen_mem (x := φ (genericPoint X'))
        (show φ (genericPoint X') ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) from
          ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩))
        (L.g (J PUnit.unit) (J' PUnit.unit) : Γ(X, L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)))) := by
  have h₀ : genericPoint X' ∈ φ ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) :=
    ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  exact fnOf_app φ h₀ _

theorem presents_pull {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) :
    Presents (pullback φ D) (L.pull φ) (fun J => unitsMap φ (r (J PUnit.unit))) := by
  refine ⟨LB.isLB_pull h.isLB φ, fun J J' hg => ?_,
    fun J x hx => isEqn_pullback φ D (h.isEqn _ _ (mem_pull.1 hx))⟩
  rw [fnOf_pull_g φ L J J' hg]
  show GlobalTheory.functionFieldMap φ _ = GlobalTheory.functionFieldMap φ _ * GlobalTheory.functionFieldMap φ _
  rw [← map_mul, ← h.isRatSec _ _ _]

end Pull

theorem genericPoint_mem_preimage {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {V : W.Opens} {y : W} (hy : y ∈ V) : genericPoint M ∈ f ⁻¹ᵁ V := by
  show f (genericPoint M) ∈ V
  have := (genericPoint_spec M).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  rw [this.eq (genericPoint_spec W)]
  exact gen_mem hy

theorem mem_sections_mul_co {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField))
    (hco : ∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x)
    {D E : CartierDiv W} {A : LB W} {rA : A.ι → W.functionFieldˣ} (hE : Presents E A rA) (t : A.Sec)
    (hP : ∀ (y : W) (i : A.ι) (hi : y ∈ A.U i) (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V')
      (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (fnOf _ (gen_mem hi) (t.f i) * co j (fnOf (f ⁻¹ᵁ V') h z)))
    {x : M.functionField} (hx : x ∈ (pullback f D).sections) (j : Fin r) :
    hE.rat t * co j x ∈ (D + E).sections := by
  refine mem_sections.2 fun y => ?_
  obtain ⟨V', hy, g, hg⟩ := D.exists_isEqn_nhds y
  have hgen := genericPoint_mem_preimage f hy
  obtain ⟨z, hz⟩ := exists_fnOf_eq hgen (f := x * GlobalTheory.functionFieldMap f g) fun m hm =>
    (isEqn_pullback f D (hg _ hm)).regularAt_iff.1 (mem_sections.1 hx m)
  obtain ⟨i, hi⟩ := exists_chart hE.isLB y
  have key := hP y i hi V' hy hgen z j
  rw [← hE.rat_mul t i (gen_mem hi), hz, mul_comm x, hco] at key
  refine ((hg y hy).add (hE.isEqn i y hi)).regularAt_iff.2 ?_
  rw [Units.val_mul]
  convert key using 1
  ring

end GlobalTheory.Cartier.PullCount

namespace GlobalTheory.Cartier.PullCount

open GlobalTheory.Cartier.DomPull GlobalTheory.Cartier.CartierDiv

theorem finrank_sections_pullback_le_mul_twist_dominant : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) [IsDominant f], IsProjOver p → ∀ {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) → (∀ x, (∀ j, co j x = 0) → x = 0) → ∀ (A : LB W), A.IsLB → ∀ (t : A.Sec), t ≠ 0 → (∀ (y : W) (i : A.ι) (hi : y ∈ A.U i) (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (fnOf _ (gen_mem hi) (t.f i) * co j (fnOf (f ⁻¹ᵁ V') h z))) → ∀ (B : LB W), B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤ r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  intro F _ M W _ _ p f _ hp r co hco hinj A hA t ht hP B hB
  obtain ⟨i₀, h₀⟩ := exists_chart hB (genericPoint W)
  have hD := presents_ofLB hB i₀ h₀
  obtain ⟨a₀, ha₀⟩ := exists_chart hA (genericPoint W)
  have hE := presents_ofLB hA a₀ ha₀
  have hDE := hD.tens hE
  have hpull := presents_pull f hD
  have hτ : hE.rat t ≠ 0 := fun e => ht (hE.rat_injective (e.trans (map_zero _).symm))
  letI iW : Algebra F Γ(W, ⊤) := algebraΓOfHom p
  letI iM : Algebra F Γ(M, ⊤) := algebraΓOfHom (f ≫ p)
  letI : Module F (B.pull f).Sec := Module.compHom _ (algebraMap F Γ(M, ⊤))
  haveI : IsScalarTower F Γ(M, ⊤) (B.pull f).Sec := IsScalarTower.of_compHom _ _ _
  letI : Module F (tens B A).Sec := Module.compHom _ (algebraMap F Γ(W, ⊤))
  haveI : IsScalarTower F Γ(W, ⊤) (tens B A).Sec := IsScalarTower.of_compHom _ _ _
  haveI : Module.Finite F (tens B A).Sec := by
    have := finite_coh_zero_twist_of_isProjOver (f := p) (fun _ => rfl) hp (isLB_tens hB hA)
    exact .equiv ((cohZeroTwistEquiv (tens B A)).restrictScalars F)
  have eW (c : F) : algebraMap F Γ(W, ⊤) c = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have eM (c : F) : algebraMap F Γ(M, ⊤) c = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (f ≫ p) ⊤ c := by
    change (f ≫ p).appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hconst (c : F) : fnOf ⊤ trivial (algebraMap F Γ(M, ⊤) c) =
      GlobalTheory.functionFieldMap f (fnOf ⊤ trivial (algebraMap F Γ(W, ⊤) c)) := by
    rw [eM, eW]
    exact (RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) c).symm
  let Ψj (j : Fin r) : (B.pull f).Sec →ₗ[F] (tens B A).Sec :=
    { toFun := fun s => hDE.secEquiv.symm
        ⟨hE.rat t * co j (hpull.rat s), mem_sections_mul_co f co hco hE t hP (hpull.rat_mem s) j⟩
      map_add' := fun s s' => by
        rw [← map_add (f := _)]
        congr 1
        apply Subtype.ext
        simp only [map_add (f := _), mul_add, Submodule.coe_add]
      map_smul' := fun c s => by
        rw [RingHom.id_apply]
        change _ = algebraMap F Γ(W, ⊤) c • (_ : (tens B A).Sec)
        rw [← map_smul]
        congr 1
        apply Subtype.ext
        change hE.rat t * co j (hpull.rat (algebraMap F Γ(M, ⊤) c • s)) =
          algebraMap F Γ(W, ⊤) c • (hE.rat t * co j (hpull.rat s))
        rw [map_smul, Algebra.smul_def, Algebra.smul_def, algebraMap_top, algebraMap_top, hconst, hco,
          mul_left_comm] }
  let Ψ : (B.pull f).Sec →ₗ[F] (Fin r → (tens B A).Sec) := LinearMap.pi Ψj
  have hΨ : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun s hs => ?_
    refine hpull.rat_injective ((hinj _ fun j => ?_).trans (map_zero _).symm)
    have e := congrArg (fun v => (hDE.secEquiv (v j) : W.functionField)) hs
    simp only [Ψ, Ψj, LinearMap.pi_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
      Pi.zero_apply, map_zero, ZeroMemClass.coe_zero] at e
    exact (mul_eq_zero.1 e).resolve_left hτ
  rw [lineBundleGlobalSectionsDim_eq_finrank, lineBundleGlobalSectionsDim_eq_finrank]
  calc Module.finrank F (B.pull f).Sec ≤ Module.finrank F (Fin r → (tens B A).Sec) :=
        LinearMap.finrank_le_finrank_of_injective hΨ
    _ = r * Module.finrank F (tens B A).Sec := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end GlobalTheory.Cartier.PullCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstJetTermsGaugeUnitMulBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

private theorem pre_lemma {Z Y X : Scheme.{0}} (x : Z ⟶ Y) (y : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) :
    ⊤ ≤ (x ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (show x.base p ∈ (⊤ : Y.Opens) from trivial)
  exact this

private theorem norm_natCast_le_one_kummer_theta_logarithms {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (f : Γ(X, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := pre_lemma _ _ _ h
  unfold valR
  rw [dite_eq_left h, dite_eq_left h']
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h (by intro _ _; trivial)]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e5 := fun w => congrArg (fun g => CommRingCat.Hom.hom g w) e2
  simp only [Scheme.Hom.appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e5
  simp only [spMap, CommRingCat.hom_comp, RingHom.comp_apply, ← e5]
  congr 1

private theorem univ_le_preimage_inf_of_univ_le {Z X : Scheme.{0}} (y : Z ⟶ X) (U V : X.Opens) (h1 : ⊤ ≤ y ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ V) :
    ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := by
  intro p hp
  exact ⟨h1 hp, h2 hp⟩

private theorem alg_lemma_5 {S : Type} [CommRing S] {n : ℕ} (a b : Fin n → S) (Ps g1 g2 g T : S)
    (h : Ps * (g1 * g2) = T) : (∑ i, a i * (Ps * b i)) * (g1 * (g2 * g)) = T * ∑ i, a i * (b i * g) := by
  rw [← h, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private theorem mul_prod_four_rearrange {S : Type} [CommRing S] (a0 a1 a2 a3 b0 b1 b2 b3 : S) :
    a0 * a1 * a2 * a3 * (b0 * b1 * b2 * b3) = (a0 * b2) * (a1 * b0) * (a2 * b1) * (a3 * b3) := by
  ring

theorem jc_eq_unit_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (C : Type) [Field C] [Algebra (FractionRing R) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR R)) (gm : GtPt D (TE R C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF R C))) gm₀ gm → ∀ (k : ℕ) (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → ∃ T : (DualNumber C)ˣ, GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left) ≠ 0 ∧ (T : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigValD D (J gm₀.b.left)) ^ k = ν.rg ^ k ∧ ∀ (s : Fam D C k) (n : ℕ) (c : Fin n → C) (f : Fin n → ∀ α : D.X, D.SecB k α), (∀ α, GeneratorPullback.SecLin D.P.L (DegPre.famφ D C α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))) → ∀ α, jc ν s gm α = (T : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (GlobalTheory.MBLow.TanExp.termV J gm₀ (f i (ν.eX α))) := by
  intro R _ _ D C _ _ N ν gm₀ gm htan hpull k J hJ
  have hb : gm.b.left = spMap (dualMap (toF R C)) ≫ gm₀.b.left := hpull.1
  have hν : ∀ (P : Sp (DualNumber C) ⟶ D.P.A.left), ⊤ ≤ P ⁻¹ᵁ D.P.L.U (ν.J (redE C ≫ P)) :=
    fun P => _root_.GlobalTheory.MBLow.TanGauge.top_le_of_redE C P _ (ν.good _)
  have hQ : redE C ≫ gm.b.left = (TF (R := R) C).hom ≫ eSec D.P.A := by
    rw [hb, ← Category.assoc, gl_redE, Category.assoc, gl_tan D gm₀ htan, ← gl_TF R C]
  have hJb : ∀ (p : Sp (DualNumber R) ⟶ D.P.A.left), ⊤ ≤ (spMap (dualMap (toF R C)) ≫ p) ⁻¹ᵁ D.P.L.U (J p) :=
    fun p => pre_lemma _ _ _ (hJ p)
  have hc0 : ⊤ ≤ gm.b.left ⁻¹ᵁ (D.P.L.U (ν.J (redE C ≫ gm.b.left)) ⊓ D.P.L.U (J gm₀.b.left)) :=
    univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb]; exact hJb _)
  have hcR : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left) :=
    top_le_wchart _ _ _ _ (fun _ => by rw [Category.id_comp, ← gl_tan D gm₀ htan]; exact pre_lemma _ _ _ (hJ _))
  refine ⟨(isUnit_trV D.P.L gm.b.left _ _ hc0 (k : ℤ)).unit, ?_, ?_, ?_⟩
  · unfold TanExp.rigValD valR
    rw [dite_eq_left hcR]
    exact (((D.rig.s _).isUnit.map _).map _).ne_zero
  · rw [IsUnit.unit_spec]
    have e1 : (trV D.P.L gm.b.left (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ)).fst =
        trV D.P.L (redE C ≫ gm.b.left) (ν.J (redE C ≫ gm.b.left)) (J gm₀.b.left) (k : ℤ) := by
      unfold trV
      exact (norm_natCast_le_one_kummer_theta_logarithms (TrivSqZeroExt.fstHom C C C).toRingHom _ _ _ hc0).symm
    have e2 : toF R C (TanExp.rigValD D (J gm₀.b.left)) = valR (TF (R := R) C).hom
        (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => J gm₀.b.left)) (D.rig.s fun _ => J gm₀.b.left).val := by
      unfold TanExp.rigValD
      rw [gl_TF R C]
      have h5 := norm_natCast_le_one_kummer_theta_logarithms (toF R C) (𝟙 _) _ (D.rig.s fun _ => J gm₀.b.left).val hcR
      rw [Category.comp_id] at h5
      exact h5.symm
    have hQ1 : ⊤ ≤ ((TF (R := R) C).hom ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U (J gm₀.b.left) := by
      rw [← hQ, hb, ← Category.assoc]; exact pre_lemma _ _ _ (hJ _)
    have e3 := _root_.GlobalTheory.MBLow.TanGauge.valR_gen_linComb D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) C).hom
      (fun _ => ν.J ((TF (R := R) C).hom ≫ eSec D.P.A)) (fun _ => J gm₀.b.left)
      (top_le_wchart _ _ _ _ (fun _ => ν.good _)) (top_le_wchart _ _ _ _ (fun _ => hQ1))
    rw [e1, e2, hQ]
    simp only [NumOf.rg, vF]
    unfold valF
    unfold valR at e3 ⊢
    rw [e3]
    simp only [Finset.univ_unique, Finset.prod_singleton, mul_pow]
    rw [trV_pow D.P.L _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (ν.good _) hQ1), _root_.one_mul]
  · intro s n c f hlin α
    have hyP : ∀ {Z : Scheme.{0}} (g : D.P.A.left ⟶ Z),
        (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left ≫
          (D.prB C).left ≫ g = gm.b.left ≫ g :=
      fun g => by rw [← Category.assoc, gl_prB']
    have hsec := _root_.GlobalTheory.MBLow.TanGauge.valR_secLin D.P.L (D.famφ C (ν.eX α)) (DegPre.famε k) (s.s (ν.eX α)) (D.famφB (ν.eX α))
      (DegPre.famε k) (fun i => f i (ν.eX α)) (D.prB C).left (fun i => scal (fst (TF (R := R) C) D.P.A).left (c i))
      (hlin _)
      (fun i => ν.J (redE C ≫ (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C)
        gm.b).left ≫ D.famφ C (ν.eX α) i))
      (fun i => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
      (by
        intro k₁ k₂ e
        rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] at e ⊢
        · rw [e]
        · rw [← hyP, ← e]
        · rw [← hyP, e]
        · rw [← hyP, ← hyP, e])
      (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE R C ⟶ TF (R := R) C) gm.b).left
      (top_le_wchart _ _ _ _ (fun i => hν _))
      (top_le_wchart _ _ _ _ (fun i => by rw [gl_prB']; exact hν _))
    have hS : ∀ i, valR gm.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
        ((f i (ν.eX α)).f fun j => ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j)) =
        (∏ j, trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) j) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) j))
          (J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) (DegPre.famε k j)) *
        dualMap (toF R C) (valR gm₀.b.left (LB.wchart D.P.L (D.famφB (ν.eX α)) fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
          ((f i (ν.eX α)).f fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))) := by
      intro i
      have hA : ⊤ ≤ gm₀.b.left ⁻¹ᵁ LB.wchart D.P.L (D.famφB (ν.eX α)) (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j)) :=
        top_le_wchart _ _ _ _ (fun j => hJ _)
      rw [_root_.GlobalTheory.MBLow.TanGauge.valR_linComb_sec D.P.L (D.famφB (ν.eX α)) (DegPre.famε k) (f i (ν.eX α)) gm.b.left _
        (fun j => J (gm₀.b.left ≫ D.famφB (ν.eX α) j))
        (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [hb, Category.assoc]; exact hJb _))]
      congr 1
      rw [hb]
      exact norm_natCast_le_one_kummer_theta_logarithms _ _ _ _ hA
    have hφ : ∀ j, D.gtφT (TE R C) gm.b (ν.eX α) j = spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j :=
      fun j => gl_gtφT_pull D (epsR R) (TE R C) (spMap (dualMap (toF R C))) (gl_hom R C) gm₀.b gm.b hb (ν.eX α) j
    have hpj : ∀ j, ⊤ ≤ D.gtφT (TE R C) gm.b (ν.eX α) j ⁻¹ᵁ D.P.L.U (pickJ (D.gtφT (TE R C) gm.b (ν.eX α))
        (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j) := by
      intro j
      obtain ⟨i', he, hj⟩ := pickJ_spec (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) j
      rw [hj, ← he, hφ i']
      exact hJb _
    unfold jc sE vE
    rw [hsec]
    simp only [gl_scal, gl_prB', hS]
    rw [_root_.GlobalTheory.MBLow.TanGauge.valR_gen_linComb D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε (gm.s (ν.eX α)) (gm.3 _) (𝟙 _) _
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (top_le_wchart _ _ _ _ (fun j => hν _)) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))]
    rw [gl_corr D.P.L (D.gtφT (TE R C) gm.b (ν.eX α)) DegPre.gtε
      (fun j => spMap (dualMap (toF R C)) ≫ D.gtφT (epsR R) gm₀.b (ν.eX α) j) DegPre.gtε _ _ (hpull.2 _)
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (pickJ (D.gtφT (TE R C) gm.b (ν.eX α)) (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)))
      (fun k₁ k₂ e => pickJ_congr _ _ e)
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ, hφ]; exact e))
      (fun k₁ k₂ e => pickJ_congr _ _ (by rw [hφ k₂]; exact e))
      (𝟙 _)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hpj j))
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [gl_pullGen D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (spMap (dualMap (toF R C)))
      _ (𝟙 _) (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp, ← hφ]; exact hpj j))]
    rw [Category.id_comp]
    rw [_root_.GlobalTheory.MBLow.TanGauge.valR_gen_linComb D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) DegPre.gtε (gm₀.s (ν.eX α)) (gm₀.3 _)
      (spMap (dualMap (toF R C))) _ (fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j))
      (top_le_wchart _ _ _ _ (fun j => by rw [← hφ]; exact hpj j)) (top_le_wchart _ _ _ _ (fun j => hJb _))]
    have hn := norm_natCast_le_one_kummer_theta_logarithms (dualMap (toF R C)) (𝟙 _) (LB.wchart D.P.L (D.gtφT (epsR R) gm₀.b (ν.eX α)) fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)) (((gm₀.s (ν.eX α)).s fun j => J (D.gtφT (epsR R) gm₀.b (ν.eX α) j)).val)
      (top_le_wchart _ _ _ _ (fun j => by rw [Category.id_comp]; exact hJ _))
    rw [Category.comp_id] at hn
    rw [hn, IsUnit.unit_spec]
    unfold TanExp.termV
    simp only [map_mul]
    refine alg_lemma_5 _ _ _ _ _ _ _ ?_
    rw [← Finset.prod_mul_distrib]
    simp only [Category.id_comp, ← hφ]
    rw [Finset.prod_congr rfl (fun j _ => _root_.GlobalTheory.MBLow.TanGauge.trV_cocycle D.P.L D.P.isLB _ _ _ _ _ (hν _) (hpj j) (by rw [hφ]; exact hJb _))]
    simp only [gl_gtφT_famφB]
    have tadd : ∀ (i : Fin 4) (a b : ℤ), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) a * trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i)
        (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i)) (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) b =
        trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) (a + b) :=
      fun i a b => trV_add _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _)) a b
    have tzero : ∀ (i : Fin 4), trV D.P.L (gm.b.left ≫ D.famφB (ν.eX α) i) (ν.J (redE C ≫ gm.b.left ≫ D.famφB (ν.eX α) i))
        (J (gm₀.b.left ≫ D.famφB (ν.eX α) i)) 0 = 1 :=
      fun i => trV_zero _ _ _ _ (univ_le_preimage_inf_of_univ_le _ _ _ (hν _) (by rw [hb, Category.assoc]; exact hJb _))
    rw [Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_prod_four_rearrange, tadd, tadd, tadd, tadd]
    have h0 : D.famφB (ν.eX α) 0 = 𝟙 _ := by
      unfold DegPre.famφB
      rfl
    simp only [sub_add_cancel, add_neg_cancel, neg_add_cancel, tzero, _root_.mul_one, h0, Category.comp_id]

end GlobalTheory.MBLow.TanGauge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePartialBlockMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem isTj_of_objMap_factor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R) (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A), m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsTj r w j o₀ o₀' ψ₀ → IsTj r w j o o' ψ := by
  intro p _ D R _ b N r w j Y₀ Y i σ₀ σ o o' o₀ o₀' m m' ψ₀ ψ hψ hfac h k _ _ _ x
  have hpu : IsUnit ((p : ℕ) : Γ(Sp k, ⊤)) := by
    have hk : IsUnit ((p : ℕ) : k) := (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero).isUnit
    have := hk.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨x₀, hx₀⟩ := hfac (Sp k) x hpu
  obtain ⟨e, he, -⟩ := m.exists_ptEquiv (Over.mk x) x₀ hx₀
  obtain ⟨e', he', -⟩ := m'.exists_ptEquiv (Over.mk x) x₀ hx₀
  have hcomp : ∀ g₀ : Over.mk x₀ ⟶ o₀.A, e g₀ ≫ ψ = e' (g₀ ≫ ψ₀) := fun g₀ => by
    ext
    rw [Over.comp_left, he, he', Over.comp_left, Category.assoc, hψ, Category.assoc]
  have hker : ∀ g₀ : Over.mk x₀ ⟶ o₀.A, e g₀ ≫ ψ = 1 ↔ g₀ ≫ ψ₀ = 1 := fun g₀ => by
    rw [hcomp]; exact map_eq_one_iff _ e'.injective
  have hact : ∀ (g₀ : Over.mk x₀ ⟶ o₀.A) (c : D.O), e g₀ ≫ o.act.act c = e (g₀ ≫ o₀.act.act c) := fun g₀ c => by
    ext
    rw [Over.comp_left, he, he, Over.comp_left, Category.assoc, Category.assoc, m.act]
  have hkill : ∀ (v : Ideal (𝓞 D.F)) (g₀ : Over.mk x₀ ⟶ o₀.A), KilledBy o v (e g₀) ↔ KilledBy o₀ v g₀ :=
    fun v g₀ => forall₂_congr fun a _ => by rw [hact]; exact map_eq_one_iff _ e.injective
  obtain ⟨h1, h2⟩ := h k x₀
  refine ⟨fun g hg hu => ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := e.surjective g
    rw [hkill]
    rw [hker] at hg
    obtain ⟨n, hn⟩ := hu
    exact h1 g₀ hg ⟨n, (hkill _ g₀).1 hn⟩
  · rw [← h2]
    exact Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv fun g₀ => by
      change _ ↔ e g₀ ≫ ψ = 1 ∧ KilledBy o w (e g₀)
      rw [hker, hkill]).symm)

end GlobalTheory.UPel.HT.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsFieldExtension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

attribute [local instance] Over.cartesianMonoidalCategory

theorem rel_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C (spMap ι ≫ z) (spMap ι ≫ p) := by
  intro E _ _ _ H Dw l Xo c Y X hFE C K K' _ _ ι z p hR
  obtain ⟨φ, k, hz, g, hs, hg, y, ψ, φ₁, f, t, t', hp, hf0, hx, hφ, hcomb⟩ := hR
  have hz' : ⊤ ≤ (spMap ι ≫ z) ⁻¹ᵁ X.F.U k := fun w _ => by
    exact hz (show spMap ι w ∈ (⊤ : (Sp K).Opens) from trivial)
  have hs' : (spMap ι ≫ z) ≫ X.π ≫ Y.s = spMap (ι.comp φ) := by
    rw [Category.assoc, hs, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  obtain ⟨g', hg'⟩ := hFE K' (ι.comp φ) (spMap ι ≫ z) k hz' hs'
  have e : spMap ι ≫ (z ≫ X.π) = (spMap ι ≫ z) ≫ X.π := (Category.assoc _ _ _).symm
  have hv : ∀ τ i, g'.v τ i = spMap (dualMap ι) ≫ g.v τ i := fun τ i => by
    have h1 : g'.v τ i = (tv (GlobalTheory.FlagMod.tanPull ι e (X.F.vecAt k z hz rfl τ i))).left := by
      rw [hg' τ i, X.F.tanPull_vecAt k ι z hz hz' rfl rfl e]
    rw [h1, hg τ i]
    rfl
  refine ⟨ι.comp φ, k, hz', g', hs', hg', y, ι.comp ψ, φ₁, f, t, fun τ i => Units.map ι.toMonoidHom (t' τ i), ?_, hf0,
    ?_, ?_, fun τ i => ?_⟩
  · rw [hp, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  · rw [Category.assoc, hx, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  · rw [hφ]; rfl
  · obtain ⟨cf, h1, h2, h3⟩ := hcomb τ i
    refine ⟨fun j => ι (cf j), by simp [h1], fun j hj => by simp [h2 j hj], ?_⟩
    have h4 := GlobalTheory.LatDRFree.comb_map Y.t ι h3
    have hd : ∀ j, spMap (dualMap ι) ≫ spMap (dualMap ψ) ≫ f.v τ j = spMap (dualMap (ι.comp ψ)) ≫ f.v τ j := fun j => by
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
      have hmap : (dualMap ι).comp (dualMap ψ) = dualMap (ι.comp ψ) := by
        ext a <;> simp [dualMap]
      rw [hmap]
    simp only [hd] at h4
    rw [hv, ← e]
    exact h4

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSub
section
noncomputable section

namespace GlobalTheory.PtDeg

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem lineDeg_eq_deg_eigLat_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)), Nonempty (SABMap t₀ Xo.univ.t y.x) → Nonempty (SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) → ∀ (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ t : 𝓞 E →+* 𝓞 K, (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act t) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s ρ hρ K _ _ _ y hy B t₀ hm1 hm2 F h hh t ht
  obtain ⟨m1⟩ := hm1
  obtain ⟨m2⟩ := hm2
  obtain ⟨π, ε, hπ, -⟩ := GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm c.F K (algebraMap c.F K)
  have ht' := _root_.GlobalTheory.ConjHostChar.conj_char E H Dw l Xo c τ K t ht
  obtain ⟨u, hu, hui, hus⟩ := _root_.GlobalTheory.PtDeg.exists_frameCoord_basis E H Dw l Xo c K y B t₀ m1 m2 F τ.1 t ht
  obtain ⟨u', hu', hui', hus'⟩ := _root_.GlobalTheory.PtDeg.exists_frameCoord_basis E H Dw l Xo c K y B t₀ m1 m2 F (conjEmb τ.1) _ ht'
  have hfin := _root_.GlobalTheory.PtDeg.rho_eq_vAdd_at_prime E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy B t₀ m1 m2 F t ht π ε hπ u u' hu hu'
  have hlat := _root_.GlobalTheory.LatDetDeg.lineDeg_det_line K h _ _ (GlobalTheory.CM.DegBound.eigLat_fg F _ _) (GlobalTheory.CM.DegBound.eigLat_fg F _ _) u u' hui hus hui'
    hus' _ (_root_.GlobalTheory.FlatPointNe.evR_sig_ne_zero E H Dw l Xo c r U x hL Z τ s K y hy) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) hfin
  have harch := _root_.GlobalTheory.PtDegArch.cInf_eq_frame_norm E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu'
  obtain ⟨hf, hd⟩ := _root_.GlobalTheory.FlatLine.lineDeg_descent c.F K π ε hπ s.cInf ρ hlat.1
  refine ⟨hf, hd.trans ?_⟩
  rw [← hlat.2]
  congr 1
  funext σ
  exact harch σ

end GlobalTheory.PtDeg
end
end

