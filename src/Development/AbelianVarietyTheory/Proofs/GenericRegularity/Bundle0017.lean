module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOneStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cabs_frBor_eq_one_of_unitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ k k' (x : (U.X k).dom) (x' : (U.X k').dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → FrBor t (U.un k x) (U.un k' x') → ∀ j, cabs (t (some j) : CAt σ) = 1 := by
  first | exact @GlobalTheory.FrameNormLie.cabs_diag_eq_one | exact GlobalTheory.FrameNormLie.cabs_diag_eq_one | (intros; apply GlobalTheory.FrameNormLie.cabs_diag_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspFormOfIntegralOverCuspForms
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem cuspForm_of_integral_over_cuspForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ (la : Wt X.Ψ r) (N k m : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (cf : ℕ → MvPolynomial (Fin N) ℂ) (g : Frame X.Ψ r → ℂ), (∀ i, w i ∈ X.SS la) → 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → X.IsSec (k • la) g → (∀ x ∈ X.dom, g x * g x ^ m + ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i = 0) → g ∈ X.SS (k • la) := by
  intro E _ _ _ r X la N k m w cf g hw hk hcf hg heq
  have hb : X.IsBddSec (k • la) g :=
    isBddSec_of_integral E r X la N k m w cf g (fun i => (hw i).1) hcf hg heq
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ :=
    siegelSpaceAlgebra_holds (E := E) r X ((m + 1) • (k • la)) ((m + 1) • (k • la)) 0
  have hterm : ∀ i ∈ Finset.range m,
      (fun x => MvPolynomial.eval (fun s => w s x) (cf i)) * g ^ (i + 1) ∈
        X.SS ((m + 1) • (k • la)) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.1 hi
    have h1 := eval_isHomogeneous_mem_cuspForms E r X la N ((m - i) * k) w (cf i) hw
      (Nat.mul_pos (Nat.sub_pos_of_lt hi') hk) (hcf i hi')
    have h2 := (bddSec_pow_succ_and_constTerm_pow_succ E r X (k • la) g hb i).1
    have h3 := (siegelSpaceAlgebra_holds (E := E) r X (((m - i) * k) • la) ((i + 1) • (k • la)) 0).2.1 _ h1 _ h2
    have e : ((m - i) * k) • la + (i + 1) • (k • la) = (m + 1) • (k • la) := by
      rw [mul_smul, ← add_smul]
      congr 1
      omega
    rwa [e] at h3
  have hsum := Finset.sum_induction _ (fun P => P ∈ X.SS ((m + 1) • (k • la)))
    (fun a b ha hb => hadd a ha b hb) h0 hterm
  have hneg := hsmul (-1) _ hsum
  refine cuspForm_of_bddSec_of_pow_succ E r X (k • la) g m hb
    ((DomCongr.bddSec_cusp_congr E r X _ _ _ fun x hx => ?_).2 hneg)
  have h := heq x hx
  have e : ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i =
      ∑ i ∈ Finset.range m, MvPolynomial.eval (fun s => w s x) (cf i) * g x ^ (i + 1) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h
  simp only [Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  linear_combination -h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorOfChartPointCdvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.TieIntegral

theorem isRigIso_iff {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) :
    IsRigIso m L' L w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl))

theorem exists_rigIso_cancel {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w'' : LB.Iso L''.L (L.L.pull n.F)) (hw : IsRigIso m L' L w) (hw'' : IsRigIso n L'' L w'') :
    ∃ w' : LB.Iso L''.L (L'.L.pull m'.F), IsRigIso m' L'' L' w' ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ G''.left) (y : Y) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        m.F (m'.F (f y)) ∈ L.L.U j → m'.F (f y) ∈ L'.L.U i → f y ∈ L''.L.U k →
        gw w'' f y j k = gw w (f ≫ m'.F) y j i * gw w' f y i k := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  rw [isRigIso_iff] at hw hw''
  obtain ⟨g, r⟩ := hw
  obtain ⟨g'', r''⟩ := hw''
  obtain ⟨w', T⟩ := exists_cancel L.isLB w w'' g g'' L'.isLB L''.isLB
  exact ⟨w', (isRigIso_iff _ _ _ _).2 ⟨T.pgen_cancel L.isLB g g'',
    T.pmaps_cancel L.isLB (fun _ => m'.e_comm) r r''⟩, T⟩

theorem gs_of_formula {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (U : X.Opens) (θ : ∀ i, Γ(X, U ⊓ L.U i)) (σ : LB.Sec L')
    (h : ∀ (j : L.ι) (k : L'.ι) (W : X'.Opens) (h₁ : W ≤ F ⁻¹ᵁ (U ⊓ L.U j))
      (h₂ : W ≤ (L.pull F).U (fun _ => j) ⊓ L'.U k),
      (F.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ.f k))
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hU : F (r z) ∈ U) (hj : F (r z) ∈ L.U j)
    (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (θ j) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  let W : X'.Opens := F ⁻¹ᵁ (U ⊓ L.U j) ⊓ L'.U k
  have h₁ : W ≤ F ⁻¹ᵁ (U ⊓ L.U j) := inf_le_left
  have h₂ : W ≤ (L.pull F).U (fun _ => j) ⊓ L'.U k := fun y hy => ⟨mem_pull.2 hy.1.2, hy.2⟩
  have hz : r z ∈ W := ⟨⟨hU, hj⟩, hk⟩
  have e := congrArg (gs r z W) (h j k W h₁ h₂)
  refine (gs_appLE F _ _ h₁ r z hz _).symm.trans (e.trans ((gs_mul r z _ hz _ _).trans ?_))
  exact congrArg₂ (· * ·) ((gs_res r z h₂ hz _).trans (gs_unit r z _ (h₂ hz) _)) (gs_res r z _ hz _)

end GlobalTheory.Reg.TieIntegral

namespace GlobalTheory.Reg


open TieIntegral in
theorem exists_generator_of_thTie :
    ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V), letI := io.toAlgebra; ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) x), Λ.ThTie s → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)), RigIso Λ.m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  intro hT E _ _ _ H Dw l Xo c O _ β Y M hPI T io f₀
  let _ := io.toAlgebra
  intro x s Λ hTie G m m2 hφ
  obtain ⟨w1, wΛ, σ, s1, r1, rΛ, hI1, hform, hg⟩ := hTie
  have hcomp : spMap ((algebraMap T.V T.Fr).comp f₀) = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hz : Λ.xF ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ (spMap f₀ ≫ M.hU.fromSpec) := by
    rw [Λ.xF_j, hcomp]; exact Category.assoc _ _ _
  obtain ⟨θ₀, hθ₀, -⟩ := thetaCore_of hT E H Dw l Xo c O β Y hPI T.V _ Λ.xF hz G m Λ.t' m2
  have hU : ⊤ ≤ (spMap f₀ ≫ M.hU.fromSpec) ⁻¹ᵁ M.U := fun y _ => by
    have : M.hU.fromSpec (spMap f₀ y) ∈ Set.range M.hU.fromSpec := ⟨_, rfl⟩
    rw [M.hU.range_fromSpec] at this
    exact this
  obtain ⟨w, θ, rw', hθ, hne⟩ := exists_sec_pull_nonzero_on_fibres E H _ _ Y.t G _ m M.U hU M.θ M.θ_mem M.θ_ne
  have hgen := (sec_generates_of_ne_zero_on_closed_fibre T.V _ G.G.hom G.PP.L θ₀ θ hθ₀ (hne _)).2
  have he : Λ.m2.cm.e = m2.cm.e ≫ m.cm.e := by
    rw [Λ.m2.base, m2.base, m.base, hcomp]; exact Category.assoc _ _ _
  obtain ⟨w2, r2, tri⟩ := exists_rigIso_cancel m.cm m2.cm Λ.m2.cm hφ.symm he Λ.t'.PP G.PP Y.t.PP w wΛ rw' rΛ
  refine ⟨θ, hgen, w1, w2, σ, s1, thfPull G.PP.L m2.φ θ, r1, r2, hI1,
    fun (i : PUnit → G.PP.L.ι) k => fn_ext fun y hy => ?_, fun j hj => rfl, hg⟩
  have hi : m2.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
  obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (m.φ (m2.φ y))
  have hyU : m.φ (m2.φ y) ∈ Y.t.G.hom ⁻¹ᵁ M.U := (congrArg (fun q => q (m2.φ y) ∈ M.U) m.cart.1.w).mpr
    (hU (show G.G.hom (m2.φ y) ∈ (⊤ : (Sp T.V).Opens) from trivial))
  have pt : Λ.m2.φ y = m.φ (m2.φ y) := congrArg (fun q => q y) hφ.symm
  have e1 := gs_of_formula w _ M.θ θ hθ (𝟙 _ ≫ m2.φ) y j (i PUnit.unit) hyU hj hi
  have e2 := gs_of_formula wΛ _ M.θ σ hform (𝟙 _) y j k (pt ▸ hyU) (pt ▸ hj) hy.2
  have e3 := tri _ (𝟙 _) y j (i PUnit.unit) k hj hi hy.2
  have e4 : (𝟙 _ ≫ m2.φ) ≫ m.φ = 𝟙 _ ≫ Λ.m2.φ := by rw [Category.assoc, hφ]
  rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
  refine (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
  refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
  exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModelChartGenericPointComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modelChart_genericPoint_component : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c), ∃ M : MChart Y, Y.j (genPt Z) ∈ M.U := by
  first | exact @GlobalTheory.GenericChart.exists_chart_genPt | exact GlobalTheory.GenericChart.exists_chart_genPt | (intros; apply GlobalTheory.GenericChart.exists_chart_genPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointVectorsIntegralInCellStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_vectors_integral_in_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ (z : FrPt Xo c T.Fr) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) z.x), Λ.LieTie (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z.u → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G), (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ Λ.t'.G.left, u' ≫ Λ.m1.φ = z.u τ i ∧ u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left := by
  first | exact @GlobalTheory.Reg.tie_vectors_integral | exact GlobalTheory.Reg.tie_vectors_integral | (intros; apply GlobalTheory.Reg.tie_vectors_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.LiftBaseChange
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.LiftBaseChange

section Bundles

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'} {F'' : X'' ⟶ X}

def IsCompIso (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (w'' : LB.Iso L'' (L.pull F'')) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : L.ι) (i : L'.ι) (k : L''.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i →
    f y ∈ L''.U k → gw w'' f y j k = gw w (f ≫ F') y j i * gw w' f y i k

theorem tie_comp (hL' : L'.IsLB) (e : F'' = F' ≫ F) {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')}
    {w'' : LB.Iso L'' (L.pull F'')} (T : IsCompIso w w' w'') (V : X.Opens) (θ : ∀ j, Γ(X, V ⊓ L.U j))
    (σ : LB.Sec L') (σ' : LB.Sec L'')
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X'') (z : Z) j k, F' (r z) ∈ L'.U j → r z ∈ L''.U k →
      gs (r ≫ F') z _ (σ.f j) = (gw w' r z j k).val * gs r z _ (σ'.f k))
    (h : ∀ (j : L.ι) (k : L'.ι) (W : X'.Opens) (h₁ : W ≤ F ⁻¹ᵁ (V ⊓ L.U j))
      (h₂ : W ≤ (L.pull F).U (fun _ => j) ⊓ L'.U k),
      (F.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ.f k))
    (j : L.ι) (k : L''.ι) (W : X''.Opens) (h₁ : W ≤ F'' ⁻¹ᵁ (V ⊓ L.U j))
    (h₂ : W ≤ (L.pull F'').U (fun _ => j) ⊓ L''.U k) :
    (F''.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w''.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ'.f k) := by
  subst e
  refine fn_ext fun y hy => ?_
  obtain ⟨i, hi⟩ := exists_chart hL' (F' y)
  have hj : F (F' y) ∈ V ⊓ L.U j := h₁ hy
  have hk : y ∈ L''.U k := (h₂ hy).2
  let W₀ : X'.Opens := F ⁻¹ᵁ (V ⊓ L.U j) ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U i)
  have hW : (𝟙 X'' ≫ F') y ∈ W₀ := ⟨hj, mem_pull.2 hj.2, hi⟩
  have e₀ := congrArg (gs (𝟙 X'' ≫ F') y W₀) (h j i W₀ inf_le_left inf_le_right)
  have e₁ : gs ((𝟙 X'' ≫ F') ≫ F) y _ (θ j) = (gw w (𝟙 X'' ≫ F') y j i).val * gs (𝟙 X'' ≫ F') y _ (σ.f i) :=
    (gs_appLE F _ _ _ _ y hW _).symm.trans (e₀.trans ((gs_mul _ y _ hW _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hW _).trans (gs_unit _ y _ hW.2 _)) (gs_res _ y _ hW _))))
  have e₂ := hσ _ (𝟙 X'') y i k hi hk
  have e₃ := T _ (𝟙 X'') y j i k hj.2 hi hk
  refine (gs_appLE _ _ _ h₁ (𝟙 _) y hy _).trans (Eq.trans ?_ (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y h₂ hy _).trans (gs_unit _ y _ (h₂ hy) _)) (gs_res _ y _ hy _)))))
  rw [← Category.assoc, e₁, e₂, ← _root_.mul_assoc, ← Units.val_mul, ← e₃]
  rfl

theorem isoMaps_comp (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (e : F'' = F' ≫ F) {w : LB.Iso L' (L.pull F)}
    {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull F'')} (T : IsCompIso w w' w'') (g : w''.IsGen)
    (σ : LB.Sec L') (σ' : LB.Sec L'')
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X'') (z : Z) j k, F' (r z) ∈ L'.U j → r z ∈ L''.U k →
      gs (r ≫ F') z _ (σ.f j) = (gw w' r z j k).val * gs r z _ (σ'.f k))
    (s : LB.Sec (L.pull F)) (hs : IsoMaps w σ s) :
    ∃ s' : LB.Sec (L.pull F''), IsoMaps w'' σ' s' ∧ ∀ (J : PUnit → L.ι) (y : X''), y ∈ (L.pull F'').U J →
      gs (𝟙 X'') y _ (s'.f J) = gs (𝟙 X'' ≫ F') y _ (s.f J) := by
  subst e
  obtain ⟨s', hs'⟩ := thf_secUp ((isGen_iff w'').1 g) hL hL'' σ'
  refine ⟨s', fun (i : PUnit → L.ι) k => fn_ext fun y hy => ?_, fun J y hy => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hs' _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  · obtain ⟨i, hi⟩ := exists_chart hL' (F' y)
    obtain ⟨k, hk⟩ := exists_chart hL'' y
    have hj : F (F' y) ∈ L.U (J PUnit.unit) := mem_pull₂.1 hy
    have hW : (𝟙 X'' ≫ F') y ∈ (L.pull F).U J ⊓ L'.U i := ⟨mem_pull.2 hj, hi⟩
    have e₀ := congrArg (gs (𝟙 X'' ≫ F') y _) (hs J i)
    have e₁ : gs (𝟙 X'' ≫ F') y _ (s.f J) =
        (gw w (𝟙 X'' ≫ F') y (J PUnit.unit) i).val * gs (𝟙 X'' ≫ F') y _ (σ.f i) :=
      (gs_res _ y _ hW _).symm.trans (e₀.trans ((gs_mul _ y _ hW _ _).trans (congrArg₂ (· * ·)
        (gs_unit _ y _ hW _) (gs_res _ y _ hW _))))
    rw [e₁, hσ _ (𝟙 X'') y i k hi hk, ← _root_.mul_assoc, ← Units.val_mul, ← T _ (𝟙 X'') y _ i k hj hi hk]
    exact hs' _ (𝟙 _) y J k hy hk

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rigIso_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) :
    RigIso m w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _ (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L)
      (fun _ => rfl))

theorem rigIso_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (n : SABMap t'' t h) (eh : h = g ≫ f)
    (eφ : n.φ = m'.φ ≫ m.φ) {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t''.PP.L (t'.PP.L.pull m'.φ)}
    (hw : RigIso m w) (hw' : RigIso m' w') :
    ∃ w'' : LB.Iso t''.PP.L (t.PP.L.pull n.φ), RigIso n w'' ∧ IsCompIso w w' w'' := by
  have ee : n.cm.e = m'.cm.e ≫ m.cm.e := by rw [n.base, m'.base, m.base, eh]
  simp only [rigIso_iff] at hw hw' ⊢
  obtain ⟨⟨F, F3, e, he, hp⟩, c, b, a, li⟩ := n
  dsimp only [SABMap.φ] at ee eφ
  subst ee eφ
  obtain ⟨w'', T⟩ := exists_comp t'.PP.isLB w w' hw.1 hw'.1 t.PP.isLB t''.PP.isLB
  exact ⟨w'', ⟨T.pgen_comp t'.PP.isLB hw.1 hw'.1, T.pmaps_comp t'.PP.isLB (fun _ => m'.cm.e_comm) hw.2 hw'.2⟩, T⟩

theorem exists_comp' {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m : SABMap t' t f) (m' : SABMap t'' t' g) (h : S'' ⟶ S) (eh : h = g ≫ f) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst eh
  exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

theorem exists_vec_lift {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {G : Over (Sp R)} {G' : Over (Sp S)}
    {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom (spMap ψ)) (v : epsR R ⟶ G) :
    ∃ v' : epsR S ⟶ G', v'.left ≫ φ = spMap (Chart.dualMapR ψ) ≫ v.left := by
  have w : (spMap (Chart.dualMapR ψ) ≫ v.left) ≫ G.hom = (epsR S).hom ≫ spMap ψ := by
    rw [Category.assoc, Over.w v]
    exact LieCombBaseChange.dualMap_over ψ
  exact ⟨Over.homMk (h.lift _ _ w) (h.lift_snd _ _ w), h.lift_fst _ _ w⟩

end GlobalTheory.LiftBaseChange

namespace GlobalTheory

open LiftBaseChange


set_option maxHeartbeats 1000000 in
theorem lift_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : R →ₐ[c.F] S), ∃ Λ' : M.Lift (ψ.toRingHom.comp f) (spMap ψ.toRingHom ≫ x), (∀ cv w, Λ.Vec cv w → Λ'.Vec (fun j => ψ (cv j)) (spMap (dualMap ψ.toRingHom) ≫ w)) ∧ ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ x))) (pm : Gx (spMap ψ.toRingHom ≫ x) ⟶ Gx x), pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left → pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left ≫ spMap ψ.toRingHom → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx (spMap ψ.toRingHom ≫ x)).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ h).hom (s.f i) = s'.f i) → Λ.ThTie s → Λ'.ThTie s' := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ S _ _ ψ
  obtain ⟨t'', p⟩ : ∃ t'' : SAB H (Sp S), Nonempty (SABMap t'' Λ.t' (spMap ψ.toRingHom)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ψ.toRingHom) Λ.t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨p⟩ := p
  have e2 : spMap (ψ.toRingHom.comp f) ≫ M.hU.fromSpec = spMap ψ.toRingHom ≫ spMap f ≫ M.hU.fromSpec := by
    rw [spMap_comp', Category.assoc]
  obtain ⟨n', hn'⟩ := exists_comp' Λ.m' p _ rfl
  obtain ⟨n1, hn1⟩ := exists_comp' Λ.m1 p _ rfl
  obtain ⟨n2, hn2⟩ := exists_comp' Λ.m2 p _ e2
  refine ⟨⟨spMap ψ.toRingHom ≫ Λ.xF, by rw [Category.assoc, Λ.xF_fst], ?_, by rw [Category.assoc, Λ.xF_j, e2],
    t'', n', n1, n2, by rw [hn1, hn', Λ.liftedChartMap_eq, Category.assoc], by rw [hn2, hn', Λ.matrix_two_by_two_congr, Category.assoc]⟩, ?_, ?_⟩
  · rw [Category.assoc, Λ.xF_snd, ← spMap_comp']
    exact congrArg spMap ψ.comp_algebraMap
  · rintro cv w ⟨v, u, hv, hc, hu⟩
    choose v' hv' using fun j => exists_vec_lift ψ.toRingHom p.cart.1 (v j)
    obtain ⟨u', hu'⟩ := exists_vec_lift ψ.toRingHom p.cart.1 u
    refine ⟨v', u', fun j => ?_, (lieComb_baseChange R S ψ.toRingHom _ _ _ p.cart _ v u cv v' u' hv' hc).1 hu', ?_⟩
    · show (v' j).left ≫ n2.φ = _
      rw [hn2, ← Category.assoc, dualMapR_comp, spMap_comp', Category.assoc (spMap _), ← hv j]
      exact (congrArg (· ≫ Λ.m2.φ) (hv' j)).trans (Category.assoc _ _ _)
    · show u'.left ≫ n1.φ = _
      rw [hn1, ← Category.assoc, ← hu]
      exact (congrArg (· ≫ Λ.m1.φ) hu').trans (Category.assoc _ _ _)
  · rintro s s' pm hp₁ hp₂ hps ⟨w1, w2, σ, s1, r1, r2, hI, hθ, hg⟩
    obtain ⟨w0, g0, r0, -⟩ := p.lin
    have R0 : RigIso p w0 := ⟨g0, r0⟩
    obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) Λ.t'.PP.isLB t''.PP.isLB σ
    obtain ⟨w1', r1', T1⟩ := rigIso_comp Λ.m1 p n1 rfl hn1 r1 R0
    obtain ⟨w2', r2', T2⟩ := rigIso_comp Λ.m2 p n2 e2 hn2 r2 R0
    obtain ⟨s1', hI', hs1'⟩ := isoMaps_comp Xo.univ.t.PP.isLB Λ.t'.PP.isLB t''.PP.isLB hn1 T1 r1'.1 σ σ' hσ' s1 hI
    refine ⟨w1', w2', σ', s1', r1', r2', hI', tie_comp Λ.t'.PP.isLB hn2 T2 _ M.θ σ σ' hσ' hθ, ?_⟩
    intro g' e₁ e₂ (j : PUnit → Xo.univ.t.PP.L.ι) hj
    have e₁' : g' ≫ (snd (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left = n1.φ := e₁
    have e₂' : g' ≫ (fst (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left = t''.G.hom := e₂
    let A := Xo.univ.t.G
    let a0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk Λ.t'.G.hom rfl
    let b0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ A := Over.homMk Λ.m1.φ Λ.m1.cart.1.w
    let g : Λ.t'.G.left ⟶ Gx x := (lift a0 b0).left
    have gf : g ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have gs' : g ≫ (snd (Over.mk x) A).left = Λ.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have sq : p.φ ≫ g = g' ≫ pm := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc]
        show p.φ ≫ g ≫ (fst (Over.mk x) A).left = g' ≫ pm ≫ (fst (Over.mk x) A).left
        rw [gf, hp₂, ← Category.assoc, e₂']
        exact p.cart.1.w
      · rw [Category.assoc, Category.assoc]
        show p.φ ≫ g ≫ (snd (Over.mk x) A).left = g' ≫ pm ≫ (snd (Over.mk x) A).left
        rw [gs', hp₁, e₁', hn1]
    have le₁ : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) := fun y hy =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) gs').mpr (mem_pull.1 hy)
    have le₂ : (PPx (spMap ψ.toRingHom ≫ x)).U (fun _ => j PUnit.unit) ≤ pm ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) :=
      fun y hy => Set.mem_iInter.2 fun _ =>
        (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) hp₁).mpr (Set.mem_iInter.1 hy 0)
    refine fn_ext fun y hy => ?_
    have hy₁ : (𝟙 _ ≫ p.φ) y ∈ (Xo.univ.t.PP.L.pull Λ.m1.φ).U j :=
      mem_pull.2 ((congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) hn1).mp (mem_pull.1 hy))
    have c₁ : (𝟙 _ ≫ p.φ) ≫ g = (𝟙 _ ≫ g') ≫ pm := by rw [Category.id_comp, Category.id_comp, sq]
    refine (hs1' j y hy).trans ((congrArg (gs (𝟙 _ ≫ p.φ) y _) (hg g gs' gf j le₁)).trans
      ((gs_appLE g _ _ le₁ _ y hy₁ _).trans ((congrArg (fun q => gs q y _ (s.f (fun _ => j PUnit.unit))) c₁).trans ?_)))
    exact (gs_appLE pm _ _ le₂ (𝟙 _ ≫ g') y (hj hy) _).symm.trans
      ((congrArg (gs (𝟙 _ ≫ g') y _) (hps _ le₂)).trans (gs_appLE g' _ _ hj (𝟙 _) y hy _).symm)

end GlobalTheory
end
end

