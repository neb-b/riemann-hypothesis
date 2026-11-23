module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductDegenerationDataSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)

noncomputable section

namespace GlobalTheory.ThmAUpper

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem xiH_base : p.R.toRealDat.toLevCh.xiH p.P.A3.A.μ0 = 1 := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  rw [← h0, p.tupXi _ (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one]

theorem xiH_twisted (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0) :
    TwistedAt D (D.plEq.symm w) ∧ p.R.toRealDat.toLevCh.xiH (p.R.mu w) =
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  have e1 : p.R.mu w = p.tupT (D.what₂.muAt (D.plEq.symm w)) := by rw [p.tupAt]; simp
  have htw : D.what₂.muAt (D.plEq.symm w) ≠ D.what₂.mu0 := fun e => hw (by rw [e1, e, h0])
  have hmt : D.what₂.muAt (D.plEq.symm w) = D.what₂.muTw (D.plEq.symm w) := (D.what₂.muAt_or _).resolve_left htw
  refine ⟨htw, ?_⟩
  rw [e1, p.tupXi _ (Or.inr ⟨_, rfl⟩), hmt, p.Tp.xi_tw]

end

theorem resChar_eq {D : D7} (w : D.what₂.places.Pl) {l : ℕ} (hl : l.Prime)
    (h : ((l : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = l := by
  by_contra hq
  have hq' := D.what₂.places.resChar_prime w
  have hnot : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal := by
    intro hin
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq' hl).2 hq)
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 D.what₂.LL) = (a : 𝓞 D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) +
        (b : 𝓞 D.what₂.LL) * ((l : ℕ) : 𝓞 D.what₂.LL) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab.symm
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hin) (Ideal.mul_mem_left _ _ h)
  have h1 : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hnot
  have h2 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ (Nat.cast_ne_zero.2 hq'.ne_zero)] at h2
  have h3 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℕ) := by
    exact_mod_cast h2
  have h4 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = 0 := by
    unfold vAdd
    rw [show ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) =
      algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) by simp, h1]
    simp
  have := D.what₂.places.ramIdx_pos w
  omega

theorem nuH_twisted {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0)
    (i j : Fin D.R.m) : nuH G (p.R.mu w) i j = nuH G p.P.A3.A.μ0 i j *
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  unfold nuH
  rw [(xiH_twisted p w hw).2, xiH_base p, mul_one, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

end GlobalTheory.ThmAUpper
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureIntegralUpdateTensorAdditive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix.CycAdd

theorem isProjOver_clos {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p) (z : X) :
    IsProjOver (closι z ≫ p) := by
  obtain ⟨N, i, hi, h⟩ := hp
  exact ⟨N, closι z ≫ i, inferInstance, by rw [Category.assoc, h]⟩

theorem int_congr {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L M : Fin D → MLine p σ} (h : ∀ ε, part L ε = part M ε) (f : CxPts p σ → ℝ) : Mix.int L f = Mix.int M f := by
  simp only [Mix.int, h]

theorem pull_update {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (i : Fin D) (A : MLine p σ) (z : X) :
    (fun j => (Function.update L i A j).pull (closι z) rfl) =
      Function.update (fun j => (L j).pull (closι z) rfl) i (A.pull (closι z) rfl) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

end GlobalTheory.Mix.CycAdd


open GlobalTheory.Mix.CycAdd in
theorem GlobalTheory.Mix.cycInt_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ) (z : X), CycIntg (Function.update L i A) f z → CycIntg (Function.update L i B) f z → cycInt (Function.update L i (A.tens B)) f z = cycInt (Function.update L i A) f z + cycInt (Function.update L i B) f z := by
  intro k _ X p σ hp D L i A B f z hA hB
  have hq := isProjOver_clos hp z
  have hI := _root_.GlobalTheory.Mix.isom_calculus k X (clos z) p (closι z ≫ p) σ (closι z) rfl
  have hparts : ∀ ε, part (fun j => (Function.update L i (A.tens B) j).pull (closι z) rfl) ε =
      part (Function.update (fun j => (L j).pull (closι z) rfl) i
        ((A.pull (closι z) rfl).tens (B.pull (closι z) rfl))) ε := by
    intro ε
    refine _root_.GlobalTheory.Mix.part_eq_of_isom k (clos z) (closι z ≫ p) σ hq D _ _ (fun j => ?_) ε
    by_cases hj : j = i
    · subst hj; simpa using hI.2.2.1 A B
    · simpa [Function.update_of_ne hj] using (_root_.GlobalTheory.Mix.isom_calculus k (clos z) (clos z) (closι z ≫ p) (closι z ≫ p) σ (𝟙 _) (Category.id_comp _)).1 ((L j).pull (closι z) rfl)
  unfold CycIntg at hA hB
  unfold cycInt
  rw [int_congr hparts, pull_update, pull_update]
  rw [pull_update] at hA hB
  exact (_root_.GlobalTheory.Mix.int_update_tens k (clos z) (closι z ≫ p) σ hq D _ i _ _ _ hA hB).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationDataIsoOfMumfordBundleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.SameLam

section Comp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D₃ : DegData R I}
  {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
  [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃] {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}
  {U₃ : UnifPre I D₃ A₃ G₃} {a : G₁ ⟶ G₂} {a' : G₂ ⟶ G₃}

theorem over_comp {b : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {b' : D₂.toPre.P.A ⟶ D₃.toPre.P.A} (h : Over₀ U₁ U₂ a b)
    (h' : Over₀ U₂ U₃ a' b') : Over₀ U₁ U₃ (a ≫ a') (b ≫ b') := fun e => by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, h' e, ← Category.assoc, h e, Category.assoc]

theorem over_id : Over₀ U₁ U₁ (𝟙 _) (𝟙 _) := fun e => by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

theorem onTorus_comp {h : D₂.toPre.X → D₁.toPre.X} {h' : D₃.toPre.X → D₂.toPre.X} (H : OnTorus U₁ U₂ a h)
    (H' : OnTorus U₂ U₃ a' h') : OnTorus U₁ U₃ (a ≫ a') (h ∘ h') := fun e => by
  obtain ⟨t, ht, et⟩ := H e
  obtain ⟨t', ht', et'⟩ := H' e
  refine ⟨t ≫ t', fun χ => unit_ext fun z _ => ?_, by
    rw [Functor.map_comp, ← Category.assoc, et, Category.assoc, et', Category.assoc]⟩
  have e₁ := congrArg (gm (𝟙 _) z ⊤) (ht (h' χ))
  have e₂ := congrArg (gm (𝟙 _ ≫ t.left) z ⊤) (ht' χ)
  refine Eq.trans ?_ e₁
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) (t ≫ t').left z ⊤ trivial _)).trans
    (Eq.trans ?_ ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)).symm)
  refine Eq.trans ?_ e₂
  refine Eq.trans ?_ ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _ ≫ t.left) t'.left z ⊤ trivial _)).symm
  rw [Over.comp_left, Category.assoc]

theorem onTorus_id : OnTorus U₁ U₁ (𝟙 _) id := fun e =>
  ⟨𝟙 _, fun χ => unit_ext fun z _ => ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans
    (gm_pull (𝟙 _) (𝟙 _) z ⊤ trivial _)).trans (by rw [Category.comp_id]; rfl), by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩

end Comp


set_option maxHeartbeats 1000000 in
theorem iso_of_lbIso_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ [Module O D'.toPre.X] (o' : D'.toPre.OAct O) (oA' : A'.OAct O), U'.toUnifPre.OLinear O o' oA' oG → LBIso (abelian₂ G U'.LG.L) (abelian₂ G U.LG.L) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom ∧ Over₀ U'.toUnifPre U.toUnifPre (𝟙 G) Φ.hom ∧ OnTorus U'.toUnifPre U.toUnifPre (𝟙 G) xe.symm ∧ (∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG lin D' A' U' _ o' oA' lin' H
  have := hR.2
  have hA := hR.1
  have := U.gen_hom
  have := U'.gen_hom
  obtain ⟨prB, hprB, qpr⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨incB, hincB, qinc⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨h, th⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨k, tk⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (𝟙 G)
    inferInstance
  have un := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre (𝟙 G)
  have un' := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D' D' A' A' G G U'.toUnifPre U'.toUnifPre (𝟙 G)
  have ipB : incB ≫ prB = 𝟙 _ := un'.1 _ _ (by have := over_comp qinc qpr; rwa [Category.comp_id] at this) over_id
  have piB : prB ≫ incB = 𝟙 _ := un.1 _ _ (by have := over_comp qpr qinc; rwa [Category.comp_id] at this) over_id
  have kh : ∀ χ, k (h χ) = χ := congrFun (un'.2 _ _ (by have := onTorus_comp tk th; rwa [Category.comp_id] at this)
    onTorus_id)
  have hk : ∀ χ, h (k χ) = χ := congrFun (un.2 _ _ (by have := onTorus_comp th tk; rwa [Category.comp_id] at this)
    onTorus_id)
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  let xe : D'.toPre.X ≃+ D.toPre.X :=
    { toFun := h, invFun := k, left_inv := kh, right_inv := hk, map_add' := h.map_add }

  have ql : ∀ x, Over₀ U.toUnifPre U.toUnifPre (oG.act x) (o.onB.act x) := fun x e => lin.q_lin e x
  have ql' : ∀ x, Over₀ U'.toUnifPre U'.toUnifPre (oG.act x) (o'.onB.act x) := fun x e => lin'.q_lin e x
  have il : ∀ x, OnTorus U.toUnifPre U.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin.i_lin e x
  have il' : ∀ x, OnTorus U'.toUnifPre U'.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin'.i_lin e x
  have linB : ∀ a, o'.onB.act a ≫ incB = incB ≫ o.onB.act a := fun a =>
    (GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (oG.act a)).1 _ _
      (by have := over_comp (ql' a) qinc; rwa [Category.comp_id] at this)
      (by have := over_comp qinc (ql a); rwa [Category.id_comp] at this)
  have linS : ∀ (b : O) χ, star b • h χ = h (star b • χ) := fun b => congrFun
    ((GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (oG.act b)).2 _ _
      (by have := onTorus_comp (il b) th; rwa [Category.comp_id] at this)
      (by have := onTorus_comp th (il' b); rwa [Category.id_comp] at this))
  have linX : ∀ (a : O) x, h (a • x) = a • h x := fun a x => by
    have := linS (star a) x
    rw [star_star] at this
    exact this.symm

  have L : Lin U.toUnifPre U'.toUnifPre (𝟙 G) prB h := ⟨inferInstance, hprB, qpr, th⟩
  have C := GlobalTheory.Mum.Two.coord_of_lin R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G) prB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A.A ⟶ A'.A, IsMonHom c ∧ Gen₀ U.toUnifPre U'.toUnifPre (𝟙 G) c :=
    ⟨U.gen.inv ≫ (Over.pullback (jK R)).map (𝟙 G) ≫ U'.gen.hom, inferInstance, by simp [Gen₀]⟩
  obtain ⟨E, eG, -⟩ := (GlobalTheory.UT.functorial_of_unif R _ hA D A G hG U).1 (𝟙 G) (𝟙 A.A) inferInstance inferInstance
    (by simp)
  have eh : ∀ y, E.h y = y := fun y =>
    congrFun (un.2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) onTorus_id) y
  have adj : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E.aG] U.LG.L) := by
    rw [eG]
    simp only [Category.comp_id]
    exact GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_linComb U.LG.isLB _ _)
  have H₂ := GlobalTheory.Mum.Two.lbIso_cubeLB_generic R _ D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G) (𝟙 G) E.aG (𝟙 G) c c
    E.aA (𝟙 _) gc gc E.ext (by simp [Gen₀]) (by rw [eG]; simp only [Category.comp_id]; exact H)
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.Mum.Two.exists_key R _ hA D D' A A' G G hG hG U U' (𝟙 G) c prB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.Mum.Two.periods_of_key R _ hA D D' A A' G G hG hG U U' (𝟙 G) c prB h hc gc L C E E
    adj H₂ Ω K
  have H' : LBIso (abelian₂ G U'.LG.L) ((abelian₂ G U.LG.L).pull (lift (fst G G ≫ 𝟙 G) (snd G G ≫ 𝟙 G) : G2 G ⟶ G2 G).left) := by
    simp only [Category.comp_id, lift_fst_snd, Over.id_left]
    exact LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) H
  have H₃ := _root_.GlobalTheory.HomMum.lbIso_descends R hA D' D A' A G G hG hG U' U (𝟙 G) (𝟙 G) incB incB inferInstance inferInstance hincB hincB
    qinc qinc H'
  have key := GlobalTheory.Mum.Two.Fac.periods_of_factor R D'.toPre D.toPre D.tau_bimult O o 1 1 incB prB h φ hincB hprB
    (by rw [piB, o.onB.map_one]) (fun χ => (C χ).imp fun _ => And.left)
    (by rw [o.onB.map_one, Category.comp_id]; exact H₃) Ω hφ
    (fun y => by rw [hhφ, eh, star_one, one_smul, one_smul, one_smul])
  rw [o.onB.map_one, Category.comp_id] at key
  obtain ⟨cφ, w, hw, ht⟩ := key
  have φh : ∀ x, φ (h x) = x := fun x => hinj ((hhφ (h x)).trans (eh _))
  refine ⟨⟨incB, prB, ipB, piB⟩, xe, hincB, qinc, tk, linB, linX, fun x => ?_, w, hw, fun a b z J J' hJ hJ' => ?_⟩
  · show D'.toPre.c x ≫ incB = D.toPre.c (h x)
    have := cφ (h x)
    rw [φh] at this
    rw [this, Category.assoc, piB, Category.comp_id]
  · have := ht (h a) (h b) z J J' hJ hJ'
    rw [φh, φh, one_smul, one_smul, one_smul] at this
    exact this

end GlobalTheory.Mum.SameLam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsSumData
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem prod_main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂), ∃ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂)) (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (q₁ : D.toPre.X →+ D₁.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSemiAbelian (G₁ ⊗ G₂) ∧ i₁ ≫ p₁ = 𝟙 _ ∧ i₂ ≫ p₂ = 𝟙 _ ∧ (∀ y, q₁ (j₁ y) = y) ∧ (∀ y, q₂ (j₂ y) = y) ∧ Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ ∧ Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ ∧ LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) ∧ GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  intro R _ _ _ hR D₁ A₁ G₁ _ _ hG₁ U₁ D₂ A₂ G₂ _ _ hG₂ U₂
  obtain ⟨D, p₁, p₂, q₁, q₂, pD⟩ := _root_.GlobalTheory.SumDeg.exists_sum R (maximalIdeal R) D₁ D₂
  obtain ⟨A, a₁, a₂, pA, -⟩ := _root_.GlobalTheory.MumProd.SumPol.exists_sum_polAV _ A₁ A₂
  obtain ⟨U, hg₁, hg₂, H⟩ := _root_.GlobalTheory.MumProdUnifSum.main R hR D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ pD pA
  haveI := pD.lim
  let e := AddEquiv.ofBijective (q₁.prod q₂) pD.xsum
  let i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A := lift (𝟙 _) (toUnit _ ≫ η[D₂.toPre.P.A]) ≫ inv (lift p₁ p₂)
  let i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A := lift (toUnit _ ≫ η[D₁.toPre.P.A]) (𝟙 _) ≫ inv (lift p₁ p₂)
  let j₁ : D₁.toPre.X →+ D.toPre.X := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
  let j₂ : D₂.toPre.X →+ D.toPre.X := e.symm.toAddMonoidHom.comp (AddMonoidHom.inr _ _)
  have hinv₁ : inv (lift p₁ p₂) ≫ p₁ = fst _ _ := by
    rw [IsIso.inv_comp_eq, lift_fst]
  have hinv₂ : inv (lift p₁ p₂) ≫ p₂ = snd _ _ := by
    rw [IsIso.inv_comp_eq, lift_snd]
  have hi₁₁ : i₁ ≫ p₁ = 𝟙 _ := by simp only [i₁, Category.assoc, hinv₁, lift_fst]
  have hi₁₂ : i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] := by simp only [i₁, Category.assoc, hinv₂, lift_snd]
  have hi₂₁ : i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] := by simp only [i₂, Category.assoc, hinv₁, lift_fst]
  have hi₂₂ : i₂ ≫ p₂ = 𝟙 _ := by simp only [i₂, Category.assoc, hinv₂, lift_snd]
  have he : ∀ z, e (e.symm z) = z := e.apply_symm_apply
  have hj₁₁ : ∀ y, q₁ (j₁ y) = y := fun y => congrArg Prod.fst (he (y, 0))
  have hj₁₂ : ∀ y, q₂ (j₁ y) = 0 := fun y => congrArg Prod.snd (he (y, 0))
  have hj₂₁ : ∀ y, q₁ (j₂ y) = 0 := fun y => congrArg Prod.fst (he (0, y))
  have hj₂₂ : ∀ y, q₂ (j₂ y) = y := fun y => congrArg Prod.snd (he (0, y))
  obtain ⟨l₁, l₂, l₃, l₄⟩ := H i₁ i₂ j₁ j₂ hi₁₁ hi₁₂ hi₂₁ hi₂₂ hj₁₁ hj₁₂ hj₂₁ hj₂₂
  exact ⟨D, A, U, i₁, p₁, i₂, p₂, j₁, q₁, j₂, q₂, _root_.GlobalTheory.SemiProd.isSemiAbelian_tensor _ G₁ G₂ hG₁ hG₂, hi₁₁, hi₂₂, hj₁₁, hj₂₂,
    _root_.GlobalTheory.MumProdAdj.adj_first_factor R _ D D₁ D₂ p₁ p₂ q₁ q₂ pD i₁ j₁ hi₁₁ hi₁₂ hj₁₁ hj₁₂,
    _root_.GlobalTheory.MumSumSnd.adj_snd R _ D D₁ D₂ p₁ p₂ q₁ q₂ pD i₂ j₂ hi₂₁ hi₂₂ hj₂₁ hj₂₂, l₁, l₂, l₃, l₄, hg₁, hg₂⟩

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendsFiniteEtaleGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.DescGal

theorem relAmple_diag_descends : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  intro X Y _ π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ _ hA₀ gp sq hP hP₀ hw hamp
  have hc : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left :=
    (GlobalTheory.DiagAmpleExt.diag_comm φ φ₂ sq).symm
  have H₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (P₀.pull φ₂) _ _ rfl) hw
  have H₂ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn P₀ (fun _ : PUnit => φ₂) (fun _ => 1) _) H₁
  have H₃ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullOut P₀ (fun _ : PUnit => (lift (𝟙 A₀) (𝟙 A₀)).left) (fun _ => 1) φ
        (fun _ => (lift (𝟙 A) (𝟙 A)).left ≫ φ₂) fun _ => hc) H₂
  exact (GlobalTheory.relAmple_kTriv_of_finite_etale_cover Y X π A₀ A φ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left)
    (P.pull (lift (𝟙 A) (𝟙 A)).left) hπ.fin hπ.etale hπ.onto hA₀ (pull_isLB hP₀ _) (pull_isLB hP _) gp H₃).1 hamp

end GlobalTheory.DescGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedArchIntegralEqSumClosureIntegrals
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem logSec_restr_secPull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} (N : HermLB p) (t : N.B.Sec)
    (i : Y ⟶ X) (σ : k →+* ℂ) :
    (MLine.ofHerm (N.restr i) σ).logSec (Cartier.secPull t i) =
      fun y => (MLine.ofHerm N σ).logSec t (ptMap i rfl σ y) :=
  funext fun y => congrArg (fun a => Real.log a / 2) ((N.φ σ).nsq_pull_secPull i rfl t y)

theorem resArch_eq_finsum_cycInt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → HermLB p) (N : HermLB p) (t : N.B.Sec) (z : X), Order.coheight z = 1 → z ∈ nonzeroLocus t → MixHt.resArch L N t z = ∑ᶠ σ : k →+* ℂ, cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t) z := by
  intro hP k _ X _ _ p e hX L N t z hz htz
  have hamb : IsAmb p := isAmb_of_isArithVar hX
  have hgen : genericPoint (clo z) ∈ nonzeroLocus (Cartier.secPull t (cloι z)) := by
    rw [Cartier.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]; exact htz
  have hd : topologicalKrullDim (clo z) = (e + 1 : ℕ) :=
    ((_root_.GlobalTheory.MixHt.dimOne k X p hamb (e + 1) hX.dim_eq).2 z (genericPoint (clo z)) hz).1
  have hamb' : IsAmb (cloι z ≫ p) := hamb.sub (cloι z)
  have hc (σ : k →+* ℂ) := (_root_.GlobalTheory.Mix.cycInt_of_closedImmersion k X (clo z) p (cloι z ≫ p) σ hX.isProjOver (cloι z) rfl e
    (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t)).2
  simp only [cloι_genericPoint] at hc
  refine (dif_pos hgen).trans ?_
  rcases isArithVar_or_isEmpty hamb' hd with hv | hE
  · refine (_root_.GlobalTheory.MixPolar.mixArch_eq_sum hP k (clo z) (cloι z ≫ p) e hv (fun a => (L a).restr (cloι z)) (N.restr (cloι z))
      (Cartier.secPull t (cloι z)) hgen).trans (finsum_congr fun σ => ?_)
    rw [hc σ, logSec_restr_secPull]
    rfl
  · refine (mixArch_eq_zero_of_isEmpty hE _ _ _).trans (finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm
    rw [hc σ]
    haveI := hE σ
    simp only [Mix.int, MeasureTheory.integral_of_isEmpty, sub_zero]

end GlobalTheory.MixHt
end

