module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMulAndFaithfulFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGroupTransportUniformisationComponent
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem exists_transport : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ (act : p.P.Gp → (uAt r v i).Comp → (uAt r v i).Comp) (tr : p.P.Gp → (uAt r v i).Comp → GL (Fin D.R.r) D.host.E),
    (∀ k, act 1 k = k) ∧ (∀ g g' k, act (g * g') k = act g (act g' k)) ∧
    (∀ g k, GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X (act g k)) (tr g k)) ∧
    (∀ g k γ, γ ∈ ((uAt r v i).X k).Γ ↔ tr g k * γ * (tr g k)⁻¹ ∈ ((uAt r v i).X (act g k)).Γ) ∧
    (∀ g g' k, tr (g * g') k * (tr g (act g' k) * tr g' k)⁻¹ ∈ ((uAt r v i).X (act (g * g') k)).Γ) ∧
    (∀ g k, act g k = k → tr g k ∈ ((uAt r v i).X k).Γ → g = 1) ∧
    (∃ a : p.P.Gp → (uAt r v i).Comp → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp)
      (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom →
      ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X (act g k)).Ψ),
        rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
            (r.lev i g⁻¹) F.1) k x =
          (a g k : ℂ) * rdU (uAt r v i) F.1 (act g k) (castFrame h2 (lact (tr g k) x))) ∧
    ∀ Lf : (uAt r v i).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E), (∀ k, Lf k = lattice₂ D ((uAt r v i).X k).Λ) →
      ∃ φ : ∀ k, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
          (Lf k ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k)))),
        ∀ (k : (uAt r v i).Comp) (g : p.P.Gp), act g k = k → ∃ n : ℤ, ∀ w : Lf k,
          ∃ hw : Matrix.mulVec (tr g k : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ Lf k,
            Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k))) ⟨_, hw⟩ =
              φ k ((r.lev i g ^ n) ((φ k).symm (Submodule.Quotient.mk w))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v
  obtain ⟨ψ, hex⟩ := _root_.GlobalTheory.ShareOn.exists_transp_all p hp r h hr i v
  have uniq := GlobalTheory.T.unique_up_to_target_group p hp r h hr i v ψ
  have one := _root_.GlobalTheory.ShareOn.isTransp_one p hp r h hr i v ψ
  have comp := _root_.GlobalTheory.ShareOn.isTransp_comp p hp r h hr i v ψ
  have gam := GlobalTheory.T.isTransport_identity_of_mem_componentGroup p hp r h hr i v ψ
  obtain ⟨lmul, linj⟩ := _root_.GlobalTheory.LevelFaithful.lev_mul_and_faithful p hp r h hr i
  have c8 := GlobalTheory.T.levelComponentTransport_reads_cuspForms_const_mul p hp r h hr i v ψ
  choose act tr htr using fun (g : p.P.Gp) k => hex (r.lev i g⁻¹) k
  have lev1 : r.lev i 1 = 1 := by
    have e := lmul 1 1
    rw [mul_one] at e
    exact (mul_eq_left.1 e.symm)
  have levinv : ∀ g, r.lev i g⁻¹ = (r.lev i g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_left (by rw [← lmul, inv_mul_cancel, lev1])
  have levmul : ∀ g g', r.lev i (g * g')⁻¹ = r.lev i g'⁻¹ * r.lev i g⁻¹ := fun g g' => by
    rw [mul_inv_rev, lmul]
  have hco : ∀ g g' k, IsTransp p r i v ψ (r.lev i (g * g')⁻¹) k (act g (act g' k)) (tr g (act g' k) * tr g' k) :=
    fun g g' k => by
      rw [levmul]
      exact comp _ _ _ _ _ _ _ (htr g' k) (htr g (act g' k))
  refine ⟨act, tr, fun k => ?_, fun g g' k => ?_, fun g k => (htr g k).1, fun g k γ => ?_, fun g g' k => ?_,
    fun g k hk hΓ => ?_, ⟨fun g k => (c8 _ _ _ _ (htr g k)).choose, fun F g k x hx h2 =>
      (c8 _ _ _ _ (htr g k)).choose_spec F x hx h2⟩, fun Lf hLf => ?_⟩
  · have e := htr 1 k
    rw [inv_one, lev1] at e
    exact (uniq _ _ _ _ _ _ e (one k)).1
  · exact (uniq _ _ _ _ _ _ (htr (g * g') k) (hco g g' k)).1
  · constructor
    · intro hγ
      have e1 := comp _ _ _ _ _ _ _ (gam k γ hγ) (htr g k)
      rw [one_mul] at e1
      have := (uniq _ _ _ _ _ _ e1 (htr g k)).2
      simpa [mul_assoc] using this
    · intro hγ
      obtain ⟨k'', b, hb⟩ := hex (r.lev i g⁻¹)⁻¹ (act g k)
      have e1 := comp _ _ _ _ _ _ _ (htr g k) hb
      rw [mul_inv_cancel] at e1
      obtain ⟨hk'', hb1⟩ := uniq _ _ _ _ _ _ e1 (one k)
      rw [hk''] at hb hb1
      have e2 := comp _ _ _ _ _ _ _ (gam _ _ hγ) hb
      have e3 := comp _ _ _ _ _ _ _ (htr g k) e2
      rw [one_mul, mul_inv_cancel] at e3
      have hb2 := (uniq _ _ _ _ _ _ e3 (one k)).2
      rw [inv_one, mul_one] at hb1 hb2
      have key : γ = (b * tr g k)⁻¹ * (b * (tr g k * γ * (tr g k)⁻¹) * tr g k) := by group
      rw [key]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb1) hb2
  · exact (uniq _ _ _ _ _ _ (htr (g * g') k) (hco g g' k)).2
  · have e1 := gam k (tr g k) hΓ
    have e2 := htr g k
    rw [hk] at e2
    have e3 := IsTransp.eq_of_eq e2 e1
    have : g⁻¹ = 1 := linj _ e3
    simpa using this
  · have keyg : ∀ g, (r.lev i g⁻¹).symm = r.lev i g ^ (1 : ℤ) := fun g => by
      rw [zpow_one, levinv]
      rfl
    obtain rfl : Lf = fun k => lattice₂ D ((uAt r v i).X k).Λ := funext hLf
    refine ⟨ψ, fun k g hk => ⟨1, fun w => ?_⟩⟩
    beta_reduce at w ⊢
    have e2 := htr g k
    rw [hk] at e2
    obtain ⟨-, -, hm⟩ := e2
    obtain ⟨hw, e⟩ := hm w
    refine ⟨hw, e.trans (congrArg (ψ k) (congrFun (congrArg DFunLike.coe (keyg g)) _))⟩

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ChartEigFrame

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.FlagMod GlobalTheory.Reg
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem tanPull_injective_of_chart {V K : Type} [CommRing V] [CommRing K] (ρ : V →+* K) (hρ : Function.Injective ρ)
    (M : MChart Y) {x : Sp V ⟶ Y.X} {x' : Sp K ⟶ Y.X} (e : spMap ρ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ M.U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ M.U) : Function.Injective (tanPull (G := Y.t.G) ρ e) := by
  intro u u' huu
  obtain ⟨cv, rfl⟩ := (vec M x h).surjective u
  obtain ⟨cv', rfl⟩ := (vec M x h).surjective u'
  rw [tanPull_vec M ρ e h h', tanPull_vec M ρ e h h'] at huu
  have := (vec M x' h').injective huu
  congr 1
  funext j
  exact hρ (congrFun this j)

theorem exists_eigFrame_of_top {X : FlagCover Y} {V K : Type} [CommRing V] [CommRing K] [Algebra c.F K]
    (ρ : V →+* K) (hρ : Function.Injective ρ) (φ : c.F →+* V) (hφ : ρ.comp φ = algebraMap c.F K)
    (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (hz' : ⊤ ≤ (spMap ρ ≫ q) ⁻¹ᵁ X.F.U k)
    (htop : ∀ σ, initSpan K (X.F.vecAt k (spMap ρ ≫ q) hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ q) ≫ X.π) σ) :
    ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (tv (X.F.vecAt k q hz rfl τ i)).left := by
  have hx : ⊤ ≤ (q ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz rfl
  have hx' : ⊤ ≤ ((spMap ρ ≫ q) ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz' rfl
  have e : spMap ρ ≫ (q ≫ X.π) = (spMap ρ ≫ q) ≫ X.π := (Category.assoc _ _ _).symm
  have hinj := tanPull_injective_of_chart ρ hρ (X.F.M k).toMChart e hx hx'
  have hpull : ∀ τ i, tanPull ρ e (X.F.vecAt k q hz rfl τ i) = X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i :=
    fun τ i => X.F.tanPull_vecAt k ρ q hz hz' rfl rfl e τ i
  have hmem : ∀ τ i, X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun τ i => by
    rw [← htop τ]
    exact Submodule.subset_span ⟨i, i.2, rfl⟩
  have hsmul : ∀ (τ : E →+* ℂ) (a : 𝓞 E) (w : TanM (q ≫ X.π) Y.t.G),
      tanPull ρ e (φ (embK c τ a) • w) = algebraMap c.F K (embK c τ a) • tanPull ρ e w := fun τ a w => by
    rw [map_smulₛₗ, ← hφ]
    rfl
  refine ⟨GlobalTheory.ShFam.EigFrame.ofVec (fun τ i => X.F.vecAt k q hz rfl τ i) (fun τ i a => ?_) (fun τ w hw => ?_),
    fun τ i => rfl⟩
  · apply hinj
    rw [tanPull_actR, hsmul, hpull]
    exact hmem τ i a
  · have hw' : tanPull ρ e w ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun a => by
      rw [← tanPull_actR, hw a, hsmul]
    rw [← htop τ] at hw'
    obtain ⟨a, -, ha⟩ := mem_initSpan.1 hw'
    obtain ⟨W, hW⟩ := X.F.uAt_split k q hz τ
    obtain ⟨cv, rfl⟩ := (vec (X.F.M k).toMChart (q ≫ X.π) hx).surjective w
    rw [X.F.sum_vecAt, tanPull_vec (X.F.M k).toMChart ρ e hx hx'] at ha
    have hc := (vec (X.F.M k).toMChart _ hx').injective ha
    rw [X.F.uAt_spMap k ρ q hz hz'] at hc
    have hWρ : W.map ρ * (X.F.uAt k q hz τ).map ρ = 1 := by
      rw [← Matrix.map_mul, hW, Matrix.map_one _ (map_zero _) (map_one _)]
    have ha2 : (W.map ρ).mulVec (fun j => ρ (cv j)) = a := by
      rw [← hc, Matrix.mulVec_mulVec, hWρ, Matrix.one_mulVec]
    refine ⟨W.mulVec cv, ?_, fun b hb => ?_⟩
    · show _ = ∑ i, _ • X.F.vecAt k q hz rfl τ i
      rw [X.F.sum_vecAt]
      congr 1
      funext j
      apply hρ
      rw [RingHom.map_mulVec]
      have : (ρ ∘ W.mulVec cv) = a := by
        rw [← ha2]
        funext i
        exact RingHom.map_mulVec ρ W cv i
      rw [this, hc]
    · have hb' : vec (X.F.M k).toMChart (q ≫ X.π) hx cv =
          vec (X.F.M k).toMChart (q ≫ X.π) hx ((X.F.uAt k q hz τ).mulVec b) := by
        rw [← X.F.sum_vecAt]
        exact hb
      have := (vec (X.F.M k).toMChart _ hx).injective hb'
      rw [this, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]

theorem exists_eigFrame_vecAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : FlagCover Y) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V), (algebraMap V K).comp φ = algebraMap c.F K → ∀ (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (yF : Sp K ⟶ Xo.XF c), yF ≫ pullback.snd _ _ = spMap (algebraMap c.F K) → (spMap (algebraMap V K) ≫ q) ≫ X.π = yF ≫ Y.j → ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (X.F.vecAt k q hz rfl τ i)).left := by
  intro E _ _ _ H Dw l Xo c O _ β Y X V K _ _ _ _ _ _ φ hφ q k hz yF hyF hpt
  have hz' : ⊤ ≤ (spMap (algebraMap V K) ≫ q) ⁻¹ᵁ X.F.U k := le_preimage_comp _ hz
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap (algebraMap V K) ≫ q) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap (algebraMap V K) ≫ q) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  exact exists_eigFrame_of_top (algebraMap V K) (IsFractionRing.injective V K) φ hφ q k hz hz'
    (key _ hpt fun σ => X.top K yF hyF _ hpt k hz' σ)

end GlobalTheory.ChartEigFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemes
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearLift

variable {S : Scheme.{0}}

theorem isMonHom_mul {H G : Over S} [GrpObj H] [GrpObj G] [IsCommMonObj G] (f g : H ⟶ G) [IsMonHom f]
    [IsMonHom g] : IsMonHom (f * g) :=
  inferInstanceAs (IsMonHom (lift f g ≫ μ[G]))

theorem isCommMonObj_of_isGrpPullback {S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    [IsCommMonObj G] {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G b φ) : IsCommMonObj G' := by
  have key : ∀ {T : Over S'} (x y : T ⟶ G'), x * y = y * x := by
    intro T x y
    let x₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    let y₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (y.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    have e₁ := h.2 T x y x₀ y₀ rfl rfl
    have e₂ := h.2 T y x y₀ x₀ rfl rfl
    have c : x₀ * y₀ = y₀ * x₀ := mul_comm _ _
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← e₁, ← e₂, c]
    · rw [Over.w, Over.w]
  refine ⟨?_⟩
  rw [mul_eq_mul, comp_mul, key]
  simp

theorem isGrpPullback_tensor {S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨GlobalTheory.AbDual.isPullback_prod m.1 n.1 h₁ h₂, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e₁ : ((x₀ * y₀) ≫ fst A B).left = ((x * y) ≫ fst A' B').left ≫ f := by
    rw [mul_comp, mul_comp]
    refine m.2 T _ _ _ _ ?_ ?_
    · simp only [Over.comp_left, hx, Category.assoc, h₁]
    · simp only [Over.comp_left, hy, Category.assoc, h₁]
  have e₂ : ((x₀ * y₀) ≫ snd A B).left = ((x * y) ≫ snd A' B').left ≫ g := by
    rw [mul_comp, mul_comp]
    refine n.2 T _ _ _ _ ?_ ?_
    · simp only [Over.comp_left, hx, Category.assoc, h₂]
    · simp only [Over.comp_left, hy, Category.assoc, h₂]
  have p : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [← Over.comp_left, e₁]
    simp only [Over.comp_left, Category.assoc, h₁]
  · rw [← Over.comp_left, e₂]
    simp only [Over.comp_left, Category.assoc, h₂]

theorem exists_lift_shear : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π →
    ∀ (g g' : ℕ) (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (i' : A₀.left ⟶ A'.left) (j' : B₀.left ⟶ B'.left),
    IsGrpPullback A₀ A' (spMap π) i' → IsGrpPullback B₀ B' (spMap π) j' → IsAbelianScheme A' → IsAbelianScheme B' →
    SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g' B'.hom →
    ∀ (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left) (h : IsPullback i A₀.hom X.hom (spMap π))
      (k : IsPullback j B₀.hom Y.hom (spMap π)), Smooth X.hom → Smooth Y.hom →
    ∀ (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
    (∀ d ∈ schemeFil (divided₂ hI) A₀ X i h.w, push (divided₂ hI) (spMap π) f₀ d ∈ schemeFil (divided₂ hI) B₀ Y j k.w) →
    ∃ φ : X ⊗ Y ⟶ Y, l ≫ φ.left = ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀).left ≫ j := by
  intro R R₀ _ _ I hI π hπ hker hL g g' A₀ B₀ _ _ A' B' _ _ i' j' hA hB hAab hBab hAg hBg X Y i j h k hX hY
    e e' he he' hie hje l hl₁ hl₂ f₀ _ hf
  haveI : IsCommMonObj B' := hBab.comm
  haveI : IsCommMonObj B₀ := isCommMonObj_of_isGrpPullback hB
  haveI hm : IsMonHom ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀) := isMonHom_mul _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, σ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀) := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, τ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀) := ⟨_, rfl⟩
  haveI : IsMonHom σ := by rw [hσ]; infer_instance
  have σ₁ : σ ≫ fst A₀ B₀ = fst A₀ B₀ := by rw [hσ, lift_fst]
  have σ₂ : σ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀) * snd A₀ B₀ := by rw [hσ, lift_snd]
  have τ₁ : τ ≫ fst A₀ B₀ = fst A₀ B₀ := by rw [hτ, lift_fst]
  have τ₂ : τ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀ := by rw [hτ, lift_snd]
  have hστ : σ ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, τ₁, σ₁, Category.id_comp]
    · rw [Category.assoc, τ₂, comp_mul, GrpObj.comp_inv, ← Category.assoc, σ₁, σ₂, inv_mul_cancel_left,
        Category.id_comp]
  have hτσ : τ ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, σ₁, τ₁, Category.id_comp]
    · rw [Category.assoc, σ₂, comp_mul, ← Category.assoc, τ₁, τ₂, mul_inv_cancel_left, Category.id_comp]
  haveI : IsIso σ := ⟨τ, hστ, hτσ⟩
  haveI : IsIso σ.left :=
    ⟨τ.left, by rw [← Over.comp_left, hστ, Over.id_left], by rw [← Over.comp_left, hτσ, Over.id_left]⟩
  obtain ⟨h₀, h₀₁, h₀₂⟩ := GlobalTheory.AbDual.exists_prod_pullback hA hB
  have hAB : IsGrpPullback (A₀ ⊗ B₀) (A' ⊗ B') (spMap π) h₀ := isGrpPullback_tensor hA hB h₀₁ h₀₂
  have hABab := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A' B' hAab hBab
  have hABg := GlobalTheory.AbDual.smooth_prod hAg hBg
  have hl : IsPullback l (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π) := GlobalTheory.AbDual.isPullback_prod h k hl₁ hl₂
  have hσl : IsPullback (σ.left ≫ l) (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π) := by
    have q := (IsPullback.of_horiz_isIso (fst := σ.left) (snd := (A₀ ⊗ B₀).hom) (f := (A₀ ⊗ B₀).hom)
      (g := 𝟙 _) ⟨by rw [Over.w, Category.comp_id]⟩).paste_horiz hl
    rwa [Category.id_comp] at q
  have hsm : Smooth (X ⊗ Y).hom := by
    haveI := hX
    haveI := hY
    rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  have hfil : schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) l hl.w =
      schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) (σ.left ≫ l) hσl.w := by
    ext d
    rw [_root_.GlobalTheory.SqLift.schemeFil_comp_iso R R₀ I (divided₂ hI) π (A₀ ⊗ B₀) (A₀ ⊗ B₀) σ (X ⊗ Y) l hl.w hσl.w d]
    have P := fun d' ↦ _root_.GlobalTheory.SqLift.ProdFil.schemeFil_tensor_iff R R₀ I (divided₂ hI) π A₀ B₀ X Y i j h.w k.w e e' he he' hie hje l hl₁ hl₂ hl.w d'
    rw [P d, P (push (divided₂ hI) (spMap π) σ d)]
    have c₁ : push (divided₂ hI) (spMap π) (fst A₀ B₀) (push (divided₂ hI) (spMap π) σ d) =
        push (divided₂ hI) (spMap π) (fst A₀ B₀) d := by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₁]
    have c₂ : push (divided₂ hI) (spMap π) (snd A₀ B₀) (push (divided₂ hI) (spMap π) σ d) =
        push (divided₂ hI) (spMap π) f₀ (push (divided₂ hI) (spMap π) (fst A₀ B₀) d) +
          push (divided₂ hI) (spMap π) (snd A₀ B₀) d := by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₂, push_mul, LinearMap.add_apply, push_comp,
        LinearMap.comp_apply]
    rw [c₁, c₂]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, add_mem (hf _ ha) hb⟩
    · rintro ⟨ha, hb⟩
      refine ⟨ha, ?_⟩
      have := sub_mem hb (hf _ ha)
      rwa [add_sub_cancel_left] at this
  obtain ⟨E, hE⟩ := hL.exists_iso hAB hABab hABg hl hσl hsm hsm hfil
  refine ⟨E.hom ≫ snd X Y, ?_⟩
  rw [Over.comp_left, ← Category.assoc, hE, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left, σ₂]

end GlobalTheory.ShearLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFiberIsAlgebraicResidueFieldOfLftStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_fiber_isAlgebraic_residueField_of_lft : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧ (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) := by
  first | exact @GlobalTheory.exists_mem_fiber_isAlgebraic_residueField | exact GlobalTheory.exists_mem_fiber_isAlgebraic_residueField | (intros; apply GlobalTheory.exists_mem_fiber_isAlgebraic_residueField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelTangentOfPullbackTangentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modelTangent_of_pullback_tangent : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) (w : epsOver V V ⟶ G.G), IsTan w → ∃ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ := by
  first | exact @GlobalTheory.TanPull.exists_tanM_of_isTan | exact GlobalTheory.TanPull.exists_tanM_of_isTan | (intros; apply GlobalTheory.TanPull.exists_tanM_of_isTan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringInValuationSubringStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finiteType_subring_in_valuationSubring : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := by
  first | exact @GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring | exact GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring | (intros; apply GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCoordOfSubsingletonPic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

noncomputable section
namespace GlobalTheory.ZM.FieldPoint

theorem exists_secCoord_of_subsingleton_pic {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} (σ : I → M.Sec)
    {A : Type} [CommRing A] [Subsingleton (CommRing.Pic A)] (x : Sp A ⟶ X) : ∃ v : I → A, SecCoord M σ x v := by
  have hL := LB.isLB_pull hM x
  obtain ⟨t, ht⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic hL
  let a := ReciprocityTheory.ChartRestriction.G.DVR.genSec t ht
  have ha : ⊤ ≤ nonzeroLocus a := (nonzeroLocus_genSec hL t ht).ge
  choose v hv using fun j => fnOn_top_bijective.2 (resG _ ha (secRatio a (secPull (σ j) x)))
  refine ⟨v, t, ht, fun i j h => ?_⟩
  have h1 := secRatio_on a (secPull (σ i) x) j (le_top.trans ha) le_rfl
  rw [resG_self, resG_self] at h1
  change _ = fnOn _ (v i) * a.f j
  rw [← resG_fnOn (le_top : _ ≤ ⊤), hv, resG_resG]
  exact h1

theorem exists_secCoord : ∀ (o : Type) [CommRing o] (m : ℕ) (K : Type) [Field K] (y : Sp K ⟶ PSpace o m),
    ∃ v : Fin (m + 1) → K, SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v :=
  fun o _ m _ _ y => exists_secCoord_of_subsingleton_pic (O1_isLB o m) _ y

end GlobalTheory.ZM.FieldPoint
end
end

