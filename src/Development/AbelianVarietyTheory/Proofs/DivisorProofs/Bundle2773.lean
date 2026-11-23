module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaPrimeIsAuxiliarySplitSquarefreeLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem vacV_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk
  obtain ⟨hSB, hne, θ, hθ, hfix⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW F E σ B a a' G X om om' hT v k hk.1 _ hSB
  have hfix₁ := GlobalTheory.T.weilOperator_latticeStabiliser_left_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ _ hSB φ₁ hφ₁ hfix hact
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v (hT.base.inert v w hin).2.2
    (GlobalTheory.T.tensorLattice_inertPlace_selfDual F E σ B a a' G X om om' hT v w hin) θ hθ _ hSB hne hfix φ₁ hφ₁ hfix₁
  have hc := GlobalTheory.T.latticeStabiliser_vacuum_eigenvalue_one_inert_place F E σ B a a' G X om om' hT v w hin hvT k hk c hact
  rw [hc, one_smul] at hact
  exact hact

theorem vac_fixed_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ k' ∈ GlobalTheory.InertSph.KAt σ G.W v,
      Acts (evFin F v) (om (k, k')) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk k' hk' r hr
  have h1 := vacV_fixed F E σ B a a' G X om om' hT v w hin hvT k hk
  have h2 := GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum F E σ B a a' G X om om' hT v w hin hvT k' hk'
  have e : om (k, k') = om (k, 1) * om (1, k') := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [e, Module.End.mul_apply, h2 r hr, h1 r hr]

end GlobalTheory.InertSph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumber
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernLine

theorem eq_homogeneousComponent {κ R : Type} [AddCommGroup R] (f : MvPolynomial κ ℝ →+ R) (D : ℕ)
    (hf : ∀ d, d ≠ D → ∀ Q : MvPolynomial κ ℝ, Q.IsHomogeneous d → f Q = 0) (P : MvPolynomial κ ℝ) :
    f P = f (homogeneousComponent D P) := by
  conv_lhs => rw [← sum_homogeneousComponent P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single D]
  · intro b _ hb
    exact hf b hb _ (homogeneousComponent_isHomogeneous b P)
  · intro hD
    rw [Finset.mem_range, not_lt] at hD
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem interPoly_eq_zero {F : Type} [Field F] (Y : Var F) {κ : Type} (Δ : κ → Y.Dv) (d : ℕ) (hd : d ≠ Y.dim)
    (Q : MvPolynomial κ ℝ) (hQ : Q.IsHomogeneous d) : Y.interPoly Δ Q = 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm' : m.degree = d := by
    have := hQ (mem_support_iff.mp hm)
    first
    | (rw [Finsupp.degree_eq_weight_one]; exact this)
    | exact this
  rw [show monomial m (AddMonoidAlgebra.coeff Q m) = AddMonoidAlgebra.coeff Q m • basisMonomials κ ℝ m by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, Var.interPoly, Module.Basis.constr_basis, dite_eq_right, smul_zero]
  rintro ⟨s, hs⟩
  apply hd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hm', ← hs, map_sum]
  simp

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hC F _ σ X κ _ Δ L r ψ hψ P
  have hR : X.interPoly Δ P = X.interPoly Δ (homogeneousComponent X.dim P) :=
    eq_homogeneousComponent (X.interPoly Δ).toAddMonoidHom X.dim (fun d hd Q hQ => interPoly_eq_zero X Δ d hd Q hQ) P
  have hL : ∀ x, dens (evalF (atlas X σ) (fun a => c1W (ψ a)) P x) =
      dens (evalF (atlas X σ) (fun a => c1W (ψ a)) (homogeneousComponent X.dim P) x) := by
    intro x
    let f : MvPolynomial κ ℝ →+ ℂ :=
      { toFun := fun Q => dens (evalF (atlas X σ) (fun a => c1W (ψ a)) Q x)
        map_zero' := by simp [evalF, LineForm.fld, dens]
        map_add' := fun Q Q' => by
          simp only [evalF, LineForm.fld, map_add (f := _), Subalgebra.coe_add]
          exact LineForm.TopInt.dens_add _ _ }
    refine eq_homogeneousComponent f X.dim (fun d hd Q hQ => ?_) P
    exact _root_.GlobalTheory.ChernCalc.dens_aeval_ofValues_offDeg X.dim κ _ d Q hQ hd
  rw [hR, ← _root_.GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly hC F σ X κ Δ L r ψ hψ _ (homogeneousComponent_isHomogeneous _ P)]
  simp only [HolAtlas.integral, LineForm.TopInt.part_congr _ hL]

end GlobalTheory.ChernLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRealPolyEqOfDbarCohomologous
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem integral_evalF_of_dbarCoh : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (ι : Type) (w w' : ι → A.Pt → Ev n), (∀ i, DbarCoh A (w i) (w' i)) → ∀ P : MvPolynomial ι ℝ, A.integral (evalF A w P) = A.integral (evalF A w' P) := by
  intro M _ _ _ _ _ _ n A ι w w' hw P
  obtain ⟨hD1, -, hDalg⟩ := dbarCoh_algebra M n A
  obtain ⟨-, hc, -, -, -⟩ := GlobalTheory.formCalculus M n A
  obtain ⟨hfin, hadd, -, -⟩ := GlobalTheory.LineForm.wInt_props M n A
  have key : DbarCoh A (fun x => aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ)))
      (fun x => aeval (fun i => w' i x) (P.map (algebraMap ℝ ℂ))) := by
    induction P using MvPolynomial.induction_on with
    | C a =>
      have h := (hDalg (a : ℂ) 1 1 1 1 hD1 hD1).1
      convert h using 1 <;> funext x <;> simp [Algebra.algebraMap_eq_smul_one]
    | add p q hp hq =>
      have h := (hDalg 1 _ _ _ _ hp hq).2.1
      convert h using 1 <;> funext x <;> simp
    | mul_X p i hp =>
      have h := (hDalg 1 _ _ _ _ hp (hw i)).2.2
      convert h using 1 <;> funext x <;> simp
  obtain ⟨-, hf', -, -, u, hu, eu⟩ := key
  have e1 : evalF A w P = evalF A w' P + A.dbar u := by
    show fld A _ = fld A _ + _
    rw [← eu]
    abel
  have hdu : A.IsForm (A.dbar u) := (hc 1 u u hu hu).2.2.2.2.1
  have int1 : ∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part α ε) := fun α h ε => by
    haveI := hfin α h ε
    exact integrable_const 1
  calc A.integral (evalF A w P) = wInt A (fun _ => 1) (evalF A w' P + A.dbar u) := by rw [wInt_one, e1]
    _ = wInt A (fun _ => 1) (evalF A w' P) + wInt A (fun _ => 1) (A.dbar u) :=
      (hadd _ _ _ hf' hdu (int1 _ hf') (int1 _ hdu)).2
    _ = A.integral (evalF A w' P) := by
      rw [wInt_one, wInt_one, (GlobalTheory.CxFormStokesBoth.stokes M n A u hu).2, add_zero]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackEqDegreeMulIntersection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_eq_deg_mul_inter : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left,
      inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  intro K _ A B f hd J _ hJ c
  by_cases hi : IsIsogeny f
  · exact GlobalTheory.T.intersection_pullback_isogeny_eq_degree_mul K A B f hi J hJ c
  · have hs : ¬ Surjective f.hom.left := by
      intro hs
      exact hi ⟨GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq K A B f hd hs, hs⟩
    rw [GlobalTheory.T.intersection_number_pullback_not_surjective_eq_zero K A B f hd hs J hJ c, deg, if_neg hi]
    simp

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemePullbackOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isAbelianScheme_pullback_of_isPullback : ∀ (S T S' : Scheme.{0}) (G : Over S) [GrpObj G] (t : T ⟶ S) (A : Over S') [GrpObj A] (a : pullback G.hom t ⟶ A.left) (g : T ⟶ S'), IsSemiAbelian G → IsAbelianScheme A → IsPullback a (pullback.snd G.hom t) A.hom g → IsAbelianScheme ((Over.pullback t).obj G) := by
  intro S T S' G _ t A _ a g hG hA sq
  exact
  { comm := by have := hG.comm; infer_instance
    smooth := by have := hG.smooth; change Smooth (pullback.snd G.hom t); infer_instance
    proper := by
      have := hA.proper; change IsProper (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
    geomConnected := by
      have := hA.geomConnected; change GeometricallyConnected (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq inferInstance }

theorem ampleDiv_closure_on_chart : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] (f : R₀) (A : Over (Sp (Localization.Away f))) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ D : CartierDiv A.left, AmpleDiv D → LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (ρ : R₀ →+* R), ρ.Flat → ρ f ≠ 0 → ∀ (G : Over (Sp R)) [GrpObj G] [IsIntegral G.left], IsSemiAbelian G → ∀ (V : G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* G.left.functionField) (D₁ : CartierDiv G.left), (∀ z : G.left, z ∈ V ↔ ρ f ∉ (G.hom z).asIdeal) → IsPullback φ (V.ι ≫ G.hom) (A.hom ≫ awayMap f) (spMap ρ) → ∀ (y : Sp (FractionRing R) ⟶ Sp (Localization.Away f)) (α : pullback G.hom (jK R) ⟶ A.left), IsGrpPullback ((Over.pullback (jK R)).obj G) A y α → (∀ (T : Scheme.{0}) (t : T ⟶ pullback G.hom (jK R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ α = t' ≫ φ) → PFF V.ι φ θ → PPull V.ι φ θ D D₁ → AmpleDiv D₁ := by
  intro R₀ _ _ f A _ _ hA D hD hsym R _ _ _ _ hR ρ hflat hρf G _ _ hG V φ θ D₁ hV hsq y α hα hcomp hff hpp
  obtain ⟨g, l, hl, sq⟩ := GlobalTheory.GenericFibreChart.exists_isPullback_generic R₀ f A R ρ hρf G V φ hV hsq
  have hGK : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    isAbelianScheme_pullback_of_isPullback _ _ _ G (jK R) A (l ≫ φ) g hG hA sq
  haveI : IsProper ((Over.pullback (jK R)).obj G).hom := hGK.proper
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hAD : IsAmpleLB (toLB D) := (ampleDiv_iff_isAmpleLB A.left D).1 hD
  have h1 : IsAmpleLB ((toLB D).pull (l ≫ φ)) := hAD.pull_of_isPullback sq
  have h3 : LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := GlobalTheory.Desc.PullOpen.lbIso_pull _ _ V φ θ D D₁ hff hpp
  have hL₁ := isLB_toLB D₁
  have h4 : LBIso ((toLB D₁).pull (pullback.fst G.hom (jK R))) ((toLB D).pull (l ≫ φ)) := by
    rw [← hl]
    exact LBIso.trans (LB.isLB_pull hL₁ _) (LB.isLB_pull (LB.isLB_pull hL₁ _) _)
      (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL₁ V.ι l).symm
      (LBIso.trans (LB.isLB_pull (LB.isLB_pull hL₁ _) _) (LB.isLB_pull (LB.isLB_pull (isLB_toLB D) _) _)
        (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.Mum.UExt.lbIso_pull h3 l)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp (isLB_toLB D) φ l))
  have h5 : IsAmpleLB ((toLB D₁).pull (pullback.fst G.hom (jK R))) := h1.of_lbIso (LB.isLB_pull hL₁ _) h4
  have h6 := (relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback (jK R)).obj G) (LB.isLB_pull hL₁ _)).2 h5
  have hlα : α = l ≫ φ := by
    have := hcomp _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rwa [Category.id_comp] at this
  have hs1 := _root_.GlobalTheory.SymGrpPull.symm_pull _ _ A ((Over.pullback (jK R)).obj G) y α hα (toLB D) (isLB_toLB D) hsym
  rw [hlα] at hs1
  have hK₁ := LB.isLB_pull hL₁ (pullback.fst G.hom (jK R))
  have hK := LB.isLB_pull (isLB_toLB D) (l ≫ φ)
  have hs2 : LBIso (((toLB D₁).pull (pullback.fst G.hom (jK R))).pull
      (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left)
      ((toLB D₁).pull (pullback.fst G.hom (jK R))) :=
    LBIso.trans (LB.isLB_pull hK₁ _) (LB.isLB_pull hK _) hK₁ (GlobalTheory.Mum.UExt.lbIso_pull h4 _)
      (LBIso.trans (LB.isLB_pull hK _) hK hK₁ hs1 h4.symm)
  haveI : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hs3 := _root_.GlobalTheory.SymGenericExt.symm_of_generic R G hG (toLB D₁) hL₁ hs2
  have h7 := _root_.GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic R hR G hG hGK (toLB D₁) hL₁ h6 hs3
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  exact (ampleDiv_iff_isAmpleLB G.left D₁).2 h7

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSmallInt
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open GlobalTheory.SeriesTie GlobalTheory.SeriesTie.BaseRat GlobalTheory.BigOn.Exp
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SerRefCore

variable {D : D7}

section Comb

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  (j : Fin D.R.m)

def AlgComb (φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
    φ = ∑ k, z k • evW YS v₀ j (g k).val

variable {YS v₀ j}

theorem AlgComb.zero : AlgComb YS v₀ j 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, by rw [Finset.univ_eq_empty, Finset.sum_empty]⟩

theorem AlgComb.add {φ ψ : GA D (Wc D j) → ℂ} (h1 : AlgComb YS v₀ j φ) (h2 : AlgComb YS v₀ j ψ) :
    AlgComb YS v₀ j (φ + ψ) := by
  obtain ⟨n, z, g, hz, rfl⟩ := h1
  obtain ⟨m, z', g', hz', rfl⟩ := h2
  refine ⟨n + m, Fin.append z z', Fin.append g g', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) k
    · rw [Fin.append_left]; exact hz a
    · rw [Fin.append_right]; exact hz' a
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem AlgComb.smul {φ : GA D (Wc D j) → ℂ} (h : AlgComb YS v₀ j φ) {a : ℂ} (ha : IsAlgebraic ℚ a) :
    AlgComb YS v₀ j (a • φ) := by
  obtain ⟨n, z, g, hz, rfl⟩ := h
  refine ⟨n, fun k => a * z k, g, fun k => ?_, ?_⟩
  · have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
    exact (hmem _).1 (mul_mem ((hmem _).2 ha) ((hmem _).2 (hz k)))
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_smul _ _ _

theorem isAlgebraic_of_smallInt {y : ℂ} (hy : y ∈ GlobalTheory.BigOn.Exp.smallInt D) : IsAlgebraic ℚ y := by
  obtain ⟨a, rfl⟩ := hy
  exact (Algebra.IsAlgebraic.isAlgebraic (algebraMap (𝓞 ↥D.LL0) ↥D.LL0 a)).algHom (embLL0 D).toRatAlgHom

theorem algComb_of_small {ρ : Setup D.ntw} {i : D.ntw.Tw} {b : Bool}
    (Φ : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ))
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (hΦ : ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → AlgComb YS v₀ j (Φ P))
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (GlobalTheory.BigOn.Exp.smallInt D) h) :
    AlgComb YS v₀ j (Φ P) := by
  have key : ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) (GlobalTheory.BigOn.Exp.smallInt D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt _ h)),
      ∃ P' ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P' = φ ∧ AlgComb YS v₀ j (Φ P') := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := honto F
      exact ⟨P', h2, h3, hΦ P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, by rw [map_zero]; exact AlgComb.zero⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, f₁⟩ := h1
      obtain ⟨P₂, a2, rfl, f₂⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, by rw [map_add (f := _)]; exact f₁.add f₂⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, f₁⟩ := h1
      refine ⟨(c : ℂ) • P₁, Submodule.smul_mem _ _ a1, ?_, ?_⟩
      · rw [map_smul]; rfl
      · rw [map_smul]; exact f₁.smul (isAlgebraic_of_smallInt c.2)
  obtain ⟨P', h1, h2, h3⟩ := key _ hP.2
  rwa [sub_eq_zero.1 (hinj (P - P') (sub_mem hP.1 h1) (by rw [map_sub, h2]; exact sub_self _))]

end Comb

end GlobalTheory.SerRefCore

namespace GlobalTheory.SerRefCore

variable {D : D7}

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem isAlgebraic_of_mem {L : IntermediateField ℚ ℂ} [FiniteDimensional ℚ L] {z : ℂ} (hz : z ∈ L) : IsAlgebraic ℚ z :=
  IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨z, hz⟩ : L))

theorem algComb_of_ratScalar (hRF : GlobalTheory.NT.RayField) {F : Face D A3.A} (fw : FWTie T Rl.toRealDat κ v₀) (hev : fw.Evaluates)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hio : IoExt Rl.toRealDat) (hpb : T.pb = Rl.C.P.pb)
    (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) {ν : ℂ} (hν : IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν)
    (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank) :
    ρ.IsDatum i j b s h P → P ∈ ρ.lat i j b (GlobalTheory.BigOn.Exp.smallInt D) h →
      AlgComb YS v₀ j (ν • ρ.theta i j b h P) := by
  intro hd hPl
  have hti := tieIn_of_fw fw
  have hrd := readsAs_one YS fw hev hV
  obtain ⟨gR, cR, cL, -, u, hu, c, ph, -, -, rfl, hsc, hrat⟩ := hν
  have hT := hti.laws
  have hB := hρ.base i j b
  have hBo := baseOf_of_realPin hcore.lev hρ hpin i j b

  obtain ⟨nδ, hnδ, hδ⟩ := de_values hρ i j b
  have hcard : Nat.card (ρ.B i j b).G.P.H ≠ 0 := Nat.card_pos.ne'
  haveI := GlobalTheory.CoverSmall.smallF_normal D hgal
  let K : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield
  have hK : ∀ {z : ℂ} {m : ℕ}, m ≠ 0 → z ^ m = 1 → z ∈ K := fun hm hz =>
    mem_algebraicClosure_iff.2 (GlobalTheory.BigOn.Exp.isAlgebraic_of_pow_eq_one hm hz)
  obtain ⟨L, _, _, hL0, -, hLr⟩ := exists_normal_roots (GlobalTheory.CoverSmall.smallF D) (k := K)
    (fun z hz => mem_algebraicClosure_iff.2 (isAlgebraic_of_mem hz)) (mul_ne_zero hcard hnδ)
  obtain ⟨C, hpd, hfr, hC⟩ := exists_goodCover_pdAt YS hRF hT hti.alg hval hray hsp (D.ntw.l i) j (κ j).n L hL0
  have hLL : (embLL0 D).fieldRange ≤ C.σ₂.fieldRange := by
    rw [hfr]; exact fun z hz => hL0 hz
  have hdat := isLevDatum_vecBase YS hT hcore hgal hval hroots hsp hρ hpin i j b hLL
    (fun p => by
      have hp1 : (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ^ (Nat.card (ρ.B i j b).G.P.H * nδ) = 1 := by
        rw [pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]
      rw [hfr]
      exact hLr _ (hK (mul_ne_zero hcard hnδ) hp1) hp1)
    (fun x => by
      have hp1 : (((ρ.B i j b).de.chi x : Circle) : ℂ) ^ (Nat.card (ρ.B i j b).G.P.H * nδ) = 1 := by
        rw [pow_mul', (hδ x).1, one_pow]
      rw [hfr]
      exact hLr _ (hK (mul_ne_zero hcard hnδ) hp1) hp1)
  rw [← hpd] at hdat
  have htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (D.ntw.l i)) (ρ.B i j b).de.chi := by
    rw [hpd]; exact isTwist_delAt Rl.C hval _ (hpin.delta i j b) hLL
  have hω := hρ.weil_base i j b
  have hω' : IsWeilDatumO Rl.ψ (Vc D j) (Wc D j) (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).2 (ρ.om i j b 1) := by
    have h1 := hω
    rw [Base.IsWeil, mul_one, Base.mu, hBo.ψ, hBo.mu0, hBo.eta] at h1
    exact h1

  have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at h2
    exact h2.le
  have hinj := _root_.GlobalTheory.ExportSeries.HarmInj.harm_inj D _ _ (ρ.B i j b).w (ρ.B i j b).F.BS hB.wt hm
  refine algComb_of_small ((ph * c) • (ρ.B i j b).theta (ρ.om i j b 1) h) hinj (fun G => ?_) (fun P hP G hPG => ?_) hPl
  · have h3 : coefFn (embLL0 D) (ρ.B i j b).w.lam (G : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) ∈
        (harm (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS).map (harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS) := by
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ _ _ hB.wt hm]
      exact Submodule.subset_span ⟨GlobalTheory.CoefModel.mapVV (embLL0 D) _ G, (Scale.coefFn_map _ _ _).symm⟩
    exact h3
  · obtain ⟨G', hG', hPG'⟩ : ∃ G' : VV D.what₂.LL (FWT.lamV D j),
        (∀ m, D.what₂.embLL (AddMonoidAlgebra.coeff (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m) ∈ (embLL0 D).fieldRange) ∧
        harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
          coefFn D.what₂.embLL (FWT.lamV D j) (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
      rw [hPG]
      have hlam := hBo.lam
      generalize (ρ.B i j b).w.lam = lam at G hlam
      subst hlam
      refine ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV D.LL0.val.toRingHom _ _ G.2⟩, fun m => ⟨AddMonoidAlgebra.coeff G.1 m, ?_⟩, ?_⟩
      · exact congrArg D.what₂.embLL (MvPolynomial.coeff_map D.LL0.val.toRingHom G.1 m).symm
      · rw [← Scale.coefFn_map, ← Scale.coefFn_map D.what₂.embLL]
        exact congrArg _ (MvPolynomial.map_map _ _ _).symm
    have hP' := hsc.ioP_eq hinj hP (ioP_mem_valSpace hcore hio (hti.hv₀ j _) hB hBo hu _) hPG'
    have hR := ((hrat C hC hLL h hd.fin _ hdat (cL j G') (Submodule.subset_span ⟨G', fun m => hLL (hG' m), rfl⟩)).2 _ _ htw).2 _ hω'
    replace hR : IsRat T j hV C (κ j) ((ph * c) • (ρ.B i j b).theta (ρ.om i j b 1) h P) :=
      (congrArg (IsRat T j hV C (κ j)) (hpin.phase_mul_thetaKO i b hP' ph (ρ.om i j b 1) h (ρ.B i j b).vecBase)).mp hR
    obtain ⟨n, z, x, hz, e⟩ := exists_sum_evW YS hti hnV hcore.lev hpb hrd hC hR fun k hk g => by
      have := GlobalTheory.ExportType.theta_type hB (D.sp.V_sig _) hω (one_mem _) (lifts_one hBo hk) h P g
      rw [show (⟨1, one_mem _⟩ : (ρ.B i j b).G.P.H) = 1 from rfl, map_one, Units.val_one, one_mul] at this
      exact congrArg ((ph * c) * ·) this
    refine ⟨n, z, x, fun k => ?_, ?_⟩
    · have hzk : z k ∈ L := by
        have := hz k
        rw [hfr] at this
        exact this
      exact isAlgebraic_of_mem hzk
    · rw [LinearMap.smul_apply, e, one_smul]

end Main

end GlobalTheory.SerRefCore
end
end

