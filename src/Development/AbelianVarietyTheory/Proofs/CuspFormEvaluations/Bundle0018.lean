module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsPtJ

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
section
namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem bor_eq_pi (Ψ : Finset (E →+* ℂ)) (r : ℕ) :
    Bor Ψ r = Set.univ.pi fun _ : Ψ => Set.univ.pi fun a : Fin r => Set.univ.pi fun c : Fin r =>
      if c < a then ({0} : Set ℂ) else if c = a then ({0}ᶜ : Set ℂ) else Set.univ := by
  ext b
  simp only [Bor, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_imp_iff]
  refine forall_congr' fun τ => ?_
  constructor
  · rintro ⟨hd, hu⟩ a c
    have hbt : (mat b τ).BlockTriangular id := fun i j h => hu i j h
    rw [Matrix.det_of_upperTriangular hbt, Finset.prod_ne_zero_iff] at hd
    split_ifs with h1 h2
    · exact hu a c h1
    · subst h2
      exact hd c (Finset.mem_univ _)
    · trivial
  · intro h
    have hu : ∀ a c : Fin r, c < a → b τ a c = 0 := by
      intro a c hc
      have := h a c
      rwa [if_pos hc] at this
    have hbt : (mat b τ).BlockTriangular id := fun i j h => hu i j h
    refine ⟨?_, hu⟩
    rw [Matrix.det_of_upperTriangular hbt, Finset.prod_ne_zero_iff]
    intro a _
    have := h a a
    rwa [if_neg (lt_irrefl a), if_pos rfl] at this


omit [NumberField E] [IsCMField E] in
theorem isPreconnected_bor (Ψ : Finset (E →+* ℂ)) (r : ℕ) : IsPreconnected (Bor Ψ r) := by
  rw [bor_eq_pi]
  refine isPreconnected_univ_pi fun _ => isPreconnected_univ_pi fun a =>
    isPreconnected_univ_pi fun c => ?_
  split_ifs
  · exact isPreconnected_singleton
  · refine (isConnected_compl_singleton_of_one_lt_rank ?_ (0 : ℂ)).isPreconnected
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  · exact isPreconnected_univ


omit [NumberField E] [IsCMField E] in
theorem continuous_rmul_pair (Ψ : Finset (E →+* ℂ)) (r : ℕ) :
    Continuous fun p : Frame Ψ r × Frame Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
  simp only [rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem frames_isConnected :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GGConnStatement (E := E) := by
  intro E _ _ _ r X
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  obtain ⟨Δ, zOf, bOf, -, hdense, -, -, hsplit, -⟩ := lu_holds r X (x0F X) ho
  have hn : Continuous (nmat X) := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    unfold nmat
    split_ifs <;> fun_prop
  have hc : Continuous (cpt X (x0F X)) :=
    (continuous_rmul_pair X.Ψ r).comp (continuous_const.prodMk hn)
  have hF : Continuous fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X (x0F X) p.1) p.2 :=
    (continuous_rmul_pair X.Ψ r).comp ((hc.comp continuous_fst).prodMk continuous_snd)
  have hcell := ((OmFConnStatement_holds r X (x0F X) ho).prod
    (isPreconnected_bor X.Ψ r)).image _ hF.continuousOn
  refine ⟨⟨_, OFC.radialRetraction_mem_chart X (x0F X) ho 0 0⟩, hcell.subset_closure ?_ ?_⟩
  · rintro _ ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    exact OntoS.dom_rmul X hz hb
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨ε0, hε0, hb⟩ := Metric.isOpen_iff.mp (FourierCoefficientDomain.isOpen_dom X) x hx
    obtain ⟨y, hy, hΔ⟩ := hdense x hx (min ε ε0) (lt_min hε hε0)
    obtain ⟨hz, hb', hye⟩ := hsplit y (hb (Metric.ball_subset_ball (min_le_right _ _) hy)) hΔ
    refine ⟨y, ⟨(zOf y, bOf y), ⟨hz, hb'⟩, hye.symm⟩, ?_⟩
    rw [dist_comm]
    exact lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFirstPartialLawSeriesOfFrames
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FramePartialLaw

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameSymmetry

section Pts

variable {S : Type} [CommRing S] (d : ℕ)

def jetRen (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m :=
  jetMap (fun q : Fin n × Fin d => MvPolynomial.X (r q.1, q.2)) fun _ => X_mem_orig _

theorem ren_copy (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (i : Fin n) :
    (jetRen (S := S) d m r).comp (jetCopy d m i) = jetCopy d m (r i) := by
  apply jet_hom_ext
  intro p
  simp only [AlgHom.comp_apply, jetRen, jetCopy, jetMap_mk, MvPolynomial.aeval_X]

theorem subst_psIn (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (g : Fin d → MvPowerSeries (Fin n × Fin d) S) :
    jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (g p.2)) =
      (jetRen d m r).comp (jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (g p.2))) := by
  have hr : (MvPolynomial.aeval fun q : Fin n × Fin d => (MvPolynomial.X (r q.1, q.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.rename fun p : Fin n × Fin d => (r p.1, p.2) := MvPolynomial.algHom_ext fun q => by simp
  apply jet_hom_ext
  intro p
  simp only [jetSubstP, jetRen, AlgHom.comp_apply, jetMap_mk, MvPolynomial.aeval_X, map_sub, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, psIn, MvPolynomial.constantCoeff_rename, hr, MvPolynomial.rename_C]

end Pts

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem pt_law (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (r : Fin 2 → Fin n) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (F p.2))) ≫ x m =
      jptG t x0 d x m (r 0) * jptG t x0 d x m (r 1) := by
  have hk : ∀ i, homAt x0 (jetRen d m r) ≫ jptG t x0 d x m i = jptG t x0 d x m (r i) := fun i => by
    rw [jptG, jptG, ← Category.assoc, homAt_comp, ren_copy]
  rw [subst_psIn, ← homAt_comp, Category.assoc, hch.law m, MonObj.comp_mul, hk, hk]

theorem th_pt {T : Over X0} (a b c : T ⟶ t.G) (I : thK) :
    (lift a (lift b c)).left ≫ thφ t.G (x3 t.G) I = (psum t.G ![a, b, c] I.down).left := by
  simp only [thφ, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a (lift b c) ≫ fst t.G (t.G ⊗ t.G) = a
    exact lift_fst _ _
  · show lift a (lift b c) ≫ (snd t.G (t.G ⊗ t.G) ≫ fst t.G t.G) = b
    rw [lift_snd_assoc, lift_fst]
  · show lift a (lift b c) ≫ (snd t.G (t.G ⊗ t.G) ≫ snd t.G t.G) = c
    rw [lift_snd_assoc, lift_snd]

theorem jetPt_trunc (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) ≫ jptG t x0 d x (m + 1) i = jptG t x0 d x m i := by
  have hc : (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) := by
    apply jet_hom_ext
    intro p
    rfl
  rw [jptG, jptG, ← Category.assoc, homAt_comp, hc, ← homAt_comp, Category.assoc, hch.trunc m]

abbrev threePts (m : ℕ) (i j k : Fin 3) : jOG x0 d m 3 ⟶ t.G ⊗ t.G ⊗ t.G :=
  lift (jptG t x0 d x m i) (lift (jptG t x0 d x m j) (jptG t x0 d x m k))

theorem threePts_trunc (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (i j k : Fin 3) :
    (ρn x0 d 3 m).left ≫ (threePts (x := x) (m + 1) i j k).left = 𝟙 _ ≫ (threePts (x := x) m i j k).left := by
  rw [← Over.comp_left, Category.id_comp, threePts, threePts, comp_lift, comp_lift, jetPt_trunc hch, jetPt_trunc hch, jetPt_trunc hch]

end Chart

end GlobalTheory.FramePartialLaw

namespace GlobalTheory


open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameSymmetry GlobalTheory.FramePartialLaw in
set_option maxHeartbeats 4000000 in
theorem exists_firstPartialLaw_series_of_frames :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ ph1 : PS S 3 d, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))) := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ hch e heg htr _
  have hL := t.PP.isLB
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x e m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp
  have hB3 : ∀ (φ1 φ2 φ3 : ℕ → Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S),
      (∀ m i j, φ1 (m + 1) i j - φ1 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ2 (m + 1) i j - φ2 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      (∀ m i j, φ3 (m + 1) i j - φ3 m i j ∈ orig S (Fin 3 × Fin d) ^ (m + 1)) →
      ∀ m y J, Good t.PP.L y J →
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e (m + 1) (φ1 (m + 1)))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e (m + 1) (φ2 (m + 1))))
            (LB.invGen t.PP.L _ _ (peG t x0 d x e (m + 1) (φ3 (m + 1)))))) (ρn x0 d 3 m).left y J =
        val (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m (φ1 m))
          (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m (φ2 m)))
            (LB.invGen t.PP.L _ _ (peG t x0 d x e m (φ3 m))))) (𝟙 _) y J := by
    intro φ1 φ2 φ3 h1 h2 h3 m y J hJ
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv, val_mul hJ, val_mul hJ, val_inv, val_inv,
      pe_trunc t x0 d htr φ1 h1 m y J hJ, pe_trunc t x0 d htr φ2 h2 m y J hJ, pe_trunc t x0 d htr φ3 h3 m y J hJ]
  obtain ⟨ph, hph⟩ := exists_series t x0 d (n := 3) _ _ _ _
    (fun m => LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (threePts (x := x) m 0 1 2).left)
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ t.cub.isGen _)
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (LB.mulGen t.PP.L _ _ _ _
        (LB.invGen t.PP.L _ _ (peG t x0 d x e m
          ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))
        (LB.invGen t.PP.L _ _ (peG t x0 d x e m
          ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hpe m _) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _)) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hpe m _))))
    (fun m U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, th_pt, pe_pt, pt_sub, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_law hch, zpow_neg, Finset.prod_inv_distrib]
      erw [prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      rw [prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left),
        prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left), prod_cube2 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
      have ha : jptG t x0 d x m (0 : Fin 3) * jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3) =
          jptG t x0 d x m (0 : Fin 3) * (jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3)) := _root_.mul_assoc _ _ _
      apply ofMul_eq
      simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
      erw [ha]
      abel!)
    (fun m y J hJ => (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J) (threePts_trunc hch m 0 1 2)).trans
      (val_pull hJ _ _ _).symm))
    (fun m y J hJ => hB3 (fun m => ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m => ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])
      (fun m i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX m _ j])
      (fun m i j => by fin_cases i <;> exact hXX m _ j) (fun m i j => by fin_cases i <;> exact hXX m _ j) m y J hJ)
  exact ⟨_, hph⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsChartGOfBasis
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChartData

open GlobalTheory.ChartJet (Q gen sq_gen)

theorem mk_psTrunc {S : Type} [CommRing S] {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    ChartJet.pj m f = Ideal.Quotient.mk _ (psTrunc m f - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m f))) := by
  have co : ∀ e : κ →₀ ℕ, e.degree < m + 1 → (psTrunc m f).coeff e = MvPowerSeries.coeff e f := fun e he => by
    have hm : e ∈ degLE m := Finset.mem_filter.2 ⟨Finset.mem_image.2
      ⟨fun i => ⟨e i, lt_of_le_of_lt (Finsupp.le_degree i e) he⟩, Finset.mem_univ _, by ext i; simp⟩, Nat.le_of_lt_succ he⟩
    rw [psTrunc, MvPolynomial.coeff_sum, Finset.sum_eq_single e (fun b _ hb => by rw [MvPolynomial.coeff_monomial, if_neg hb])
      (fun h => absurd hm h), MvPolynomial.coeff_monomial, if_pos rfl]
  have c0 : MvPolynomial.constantCoeff (psTrunc m f) = 0 := (co 0 (by simp)).trans hf
  rw [c0, map_zero, sub_zero]
  exact ChartJet.pj_eq_mk.2 fun e he => (co e he).symm

theorem jetMap_zR {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (h) (s : κ) :
    (jetMap φ h : Jet S κ m →ₐ[S] Jet S κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X s)) = Ideal.Quotient.mk _ (φ s) := by
  show Ideal.Quotient.mkₐ S _ (MvPolynomial.aeval φ (MvPolynomial.X s)) = _
  rw [MvPolynomial.aeval_X]; rfl

theorem subst_zR {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (p : Q S d n) (s : Fin 1 × Fin d) :
    jetSubstP m (fun s : Fin 1 × Fin d => psTrunc m (p.1 s.2)) (Chart.zR m s) = ChartJet.pj m (p.1 s.2) :=
  (jetMap_zR m _ _ s).trans (mk_psTrunc m _ (p.2 _)).symm

theorem copy_zR {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (i : Fin n) (s : Fin 1 × Fin d) :
    jetCopy (S := S) d m i (Chart.zR m s) = ChartJet.pj m ((gen i : Q S d n).1 s.2) :=
  (jetMap_zR m _ _ s).trans (ChartJet.pj_X m (i, s.2)).symm


set_option maxHeartbeats 1600000 in
theorem exists_isChartG_of_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)), (∀ ℓ, IsTanAtG t x0 (tg ℓ)) → (∀ w, IsTanAtG t x0 w → ∃! a : κ → S, IsCombAtG t x0 (m := Fintype.card κ) (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) → ∃ (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧ IsChartG t x0 d G.F A.act tg uvec x := by
  classical
  intro E _ _ _ H X0 t S _ x0 κ _ tg htan hb
  have hp := isGrpPullback_pullback t.G x0
  have := t.semi.smooth
  have : Smooth ((Over.pullback x0).obj t.G).hom :=
    smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  let φ := pullback.fst t.G.hom x0
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 →
      (epsR S ⟶ (Over.pullback x0).obj t.G) := fun w h => Over.homMk (pullback.lift w _ h) (pullback.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => pullback.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ (Over.pullback x0).obj t.G}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (pullback.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have tan : ∀ w : epsR S ⟶ (Over.pullback x0).obj t.G, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ φ) := fun w => by
    have e : (1 : Chart.sp (R₀ := S) S ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x0 ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => pullback.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this
  let e := Fintype.equivFin κ
  let v : Fin (Fintype.card κ) → (epsR S ⟶ (Over.pullback x0).obj t.G) := fun i => up (tg (e.symm i)) (htan _).1
  have hv : (fun i => (v i).left ≫ φ) = fun i => tg (e.symm i) := funext fun i => hup _ _
  have hB : IsLieBasis v := ⟨fun i => (tan _).2 (by rw [hup]; exact htan _), fun w hw => by
    obtain ⟨a, ha, hu⟩ := hb _ ((tan w).1 hw)
    refine ⟨fun i => a (e.symm i), (comb _ _ _).2 (hv ▸ ha), fun c hc => ?_⟩
    have := hu (fun l => c (e l)) (by simpa only [e, Equiv.apply_symm_apply] using hv ▸ (comb _ _ _).1 hc)
    funext i; rw [← this]; simp⟩
  obtain ⟨x, hx, hxv'⟩ := GlobalTheory.exists_isUnivChart_of_isLieBasis S ((Over.pullback x0).obj t.G) this _ v hB
  have hxv := fun j => (hxv' j).symm
  obtain ⟨F, A, hF, hA⟩ := ChartJet.exists_series hx (OAct.pullback x0 t.G t.act)
  have sub : ∀ {n} m (p : Q S (Fintype.card κ) n) (g : Jet S (Fin 1 × Fin (Fintype.card κ)) m →ₐ[S] Jet S (Fin n × _) m),
      (∀ s, g (Chart.zR m s) = ChartJet.pj m (p.1 s.2)) →
      homAt x0 g ≫ pushPt hp.1.w (ChartJet.ptJ x m (gen 0)) = pushPt hp.1.w (ChartJet.ptJ x m p) := fun m p g hg => by
    have e₁ : g = ChartJet.jQ m ![p] := Chart.jet_ext fun s => (hg s).trans (by
      obtain ⟨i, j⟩ := s
      obtain rfl := Subsingleton.elim i 0
      exact (ChartJet.jS_zR m (fun s : Fin 1 × _ => ((![p] : Fin 1 → _) s.1).1 s.2) (fun s => ((![p] : Fin 1 → _) s.1).2 s.2)
        (0, j)).symm)
    have e₂ := ChartJet.ptJ_sq x m ![p] (gen 0)
    rw [sq_gen, ← e₁] at e₂
    exact Over.OverMorphism.ext ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left ≫ φ) e₂))
  have sp := fun {n} m (p : Q S (Fintype.card κ) n) => subst_zR m p
  have cp : ∀ {n} m (i : Fin n), jptG t x0 _ (fun m => pushPt hp.1.w (ChartJet.ptJ x m (gen 0))) m i =
      pushPt hp.1.w (ChartJet.ptJ x m (gen i)) := fun m i => sub m (gen i) _ (copy_zR m i)
  refine ⟨_, F, A, fun l => Pi.single (e l) 1, fun m => pushPt hp.1.w (ChartJet.ptJ x m (gen 0)), rfl,
    fun l j => by simp only [Pi.single_apply, Fin.ext_iff, e], fun m => ?_, fun m => ?_,
    fun m => ?_, fun m a => ?_, fun l => ?_, fun w => ?_⟩
  · exact Over.OverMorphism.ext ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q.left ≫ φ) (ChartJet.ptJ_aug hx m (gen 0))).trans (one _)))
  · exact Over.OverMorphism.ext ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q.left ≫ φ) (ChartJet.ptJ_trunc hx m (gen 0))))
  · rw [cp, cp]
    exact (sub m ⟨F.F, F.const⟩ _ (sp m _)).trans ((congrArg _ (hF m)).trans (map_mul (pushHom hp _) _ _))
  · refine Eq.trans ?_ ((sub m ⟨A.act a, A.const a⟩ _ (sp m _)).trans (congrArg _ (hA a m))).symm
    exact Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (pullback.lift_fst _ _ _ : ((OAct.pullback x0 t.G t.act).act a).left ≫ φ = φ ≫ (t.act.act a).left).symm).trans
      (Category.assoc _ _ _).symm))
  · have h := (comb _ _ _).1 (ChartJet.comb_single hx hxv (e l))
    rw [hup, Equiv.symm_apply_apply] at h
    convert h using 2 with j
    let T : Chart.JetR S (Fin 1 × Fin (Fintype.card κ)) 1 →ₐ[S] DualNumber S := (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (Fintype.card κ)) (0 + 1) →ₐ[S] DualNumber S)
    have e₁ : T.comp (ChartJet.jP 1 (gen 0 : Q S _ 1)) = Chart.dualLift (Pi.single j 1) := Chart.jet_ext fun i => by
      rw [AlgHom.comp_apply, ChartJet.jP_zR, Chart.dualLift_zR]
      refine (congrArg T (ChartJet.pj_X 1 ((0 : Fin 1), i))).trans ?_
      show MvPolynomial.aeval (fun i => if i = ((0 : Fin 1), j) then (DualNumber.eps : DualNumber S) else 0)
        (MvPolynomial.X ((0 : Fin 1), i)) = _
      rw [MvPolynomial.aeval_X]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, Pi.single_eq_same]; rfl
      · rw [if_neg (fun h => hij (Prod.ext_iff.1 h).2), Pi.single_eq_of_ne hij, TrivSqZeroExt.inr_zero]
    have e₂ : Chart.spMap T ≫ ChartJet.ptJ x 1 (gen 0) = v j := by
      rw [hxv, ← e₁, ← Chart.spMap_comp, Category.assoc]; rfl
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left ≫ φ) e₂)
  · refine ⟨fun l => w (e l), fun j => ?_, fun a ha => funext fun l => ?_⟩
    · rw [Finset.sum_eq_single (e.symm j) (fun b _ hb => by
        rw [Pi.single_eq_of_ne (fun h => hb (by rw [h, Equiv.symm_apply_apply])), mul_zero]) (by simp)]
      simp
    · rw [← ha, Finset.sum_eq_single l (fun b _ hb => by
        rw [Pi.single_eq_of_ne (fun h => hb (e.injective h).symm), mul_zero]) (by simp)]
      simp

end GlobalTheory.ChartData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameRigidificationOfCanonicalAxes
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ThetaVal

theorem jetAug_comp_jetSubstP {S A B : Type} [CommRing S] (m : ℕ) (φ : A → MvPolynomial B S) :
    (jetAug : Jet S B m →ₐ[S] S).comp (jetSubstP m φ) = (jetAug : Jet S A m →ₐ[S] S) := by
  apply Ideal.Quotient.algHom_ext S
  apply MvPolynomial.algHom_ext
  intro i
  simp [jetSubstP, jetAug, jetMap, liftJet]
  erw [Ideal.Quotient.lift_mk]
  simp

private theorem homAt_comp_homAt_eq_homAt_comp {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A]
    [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    Formalism.L2.Pj.homAt x0 g ≫ Formalism.L2.Pj.homAt x0 f = Formalism.L2.Pj.homAt x0 (g.comp f) := by
  unfold Formalism.L2.Pj.homAt
  ext : 1
  simp only [Over.comp_left, Over.homMk_left]
  unfold spMap
  rw [← Spec.map_comp]
  rfl


set_option maxHeartbeats 4000000 in
theorem rig_of_frAxes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∀ wP : PrimTyG t, IsPrimG t wP → Rig0G t x0 d x act e wP := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x hF hact hch e hgen htr hax wP hP
  have hL : t.PP.L.IsLB := t.PP.isLB
  unfold Rig0G eLG peG
  apply corr_of_val hL
  intro y J hJ
  rw [val_pull hJ, val_mul hJ, val_pull hJ]
  rw [val_pull hJ (φ := cφG t ![jptG t x0 d x 0 (0 : Fin 2), jptG t x0 d x 0 (1 : Fin 2)]) (ε := cε 2) (t := e 0)]
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.val_rigT _ _ _ _ _ _ _ hJ]
  have hA : (𝟙 _ ≫ Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S))) ≫
      (x 0).left = (overAt x0 S).hom ≫ eSec t.G := by
    rw [Category.id_comp, ← Over.comp_left, hch.zero 0]
    rfl
  have hB : ∀ ψ : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S,
      (𝟙 _ ≫ Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S))) ≫
        Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetSubstP 0 ψ)) =
        Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 2 × Fin d) 0 →ₐ[S] S)) := by
    intro ψ
    rw [Category.id_comp, ← Over.comp_left, homAt_comp_homAt_eq_homAt_comp, jetAug_comp_jetSubstP]
  rw [hA, hB]
  rw [← hB (fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S)
      p.1 p.2)]
  rw [← val_pull hJ (φ := cφG t ![jptG t x0 d x 0 (0 : Fin 2), jptG t x0 d x 0 (1 : Fin 2)]) (ε := cε 2)
    (t := e 0)]
  rw [val_corr hJ (hax 0).1, val_one, _root_.mul_one]
  rw [← val_pull hJ wP (eSec t.G), val_corr hJ hP.2, Category.id_comp]

end GlobalTheory.ThetaVal
end
end

