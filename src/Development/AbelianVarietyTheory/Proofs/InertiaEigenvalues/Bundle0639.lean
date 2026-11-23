module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaximalIsotropicDoubled
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangiansTransverseEqGraphsRationalUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Graphs

variable {D : D7}

def graphSub (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Submodule D.host.E ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearMap.range (LinearMap.prod LinearMap.id (Matrix.mulVecLin c))

theorem mem_graphSub {W : HSp D} {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    {y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)} : y ∈ graphSub W c ↔ y.2 = c *ᵥ y.1 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro h
    exact ⟨y.1, Prod.ext rfl (by simp [h])⟩

theorem cT_eq (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) c = cᴴ := by
  funext i j
  rfl

theorem star_dot (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (x x' : Fin W.rank → D.host.E) :
    star (c *ᵥ x) ⬝ᵥ W.gram *ᵥ (c *ᵥ x') = star x ⬝ᵥ (cᴴ * W.gram * c) *ᵥ x' := by
  rw [Matrix.star_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

def graphLag (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : Lag W :=
  ⟨graphSub W g, by
    rw [graphSub, LinearMap.finrank_range_of_inj (fun x y h => congrArg Prod.fst h)]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
        W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
    rw [cT_eq] at h
    show star x ⬝ᵥ W.gram *ᵥ y = star ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x) ⬝ᵥ
      W.gram *ᵥ ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ y)
    rw [star_dot, h]⟩

theorem graphLag_bot (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    (graphLag W g hg).1.comap (LinearMap.inl D.host.E _ _) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h : (0 : Fin W.rank → D.host.E) = (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x :=
    mem_graphSub.1 (Submodule.mem_comap.1 hx)
  have h2 := congrArg (((g⁻¹ : GL (Fin W.rank) D.host.E) : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ ·) h
  simpa [Matrix.mulVec_mulVec] using h2.symm

theorem herm' (W : HSp D) : W.gramᵀ.map (starRingAut : D.host.E ≃+* D.host.E) = W.gram := by
  have h := GlobalTheory.AutFunCounterexample.gram_herm W
  funext i j
  exact congrFun (congrFun h i) j

theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem exists_rat (W : HSp D) (γ : GQ W) : ∃ g : GL (Fin W.rank) D.host.E,
    g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram ∧ Formalism.UG.bc (incA D) g = matHom W (γ : GA D W) := by
  have h : matHom W (γ : GA D W) ∈ HFin (AF D.host.F) D.sp.cm.sig W.gram := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 h
  exact ⟨g, hg, e⟩

def ratG (W : HSp D) (γ : GQ W) : GL (Fin W.rank) D.host.E := (exists_rat W γ).choose

theorem ratG_mem (W : HSp D) (γ : GQ W) :
    ratG W γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := (exists_rat W γ).choose_spec.1

theorem mt_ratG (W : HSp D) (γ : GQ W) :
    Formalism.L2.Theta.mt W (γ : GA D W) = (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) := by
  rw [Formalism.L2.Theta.mt, ← (exists_rat W γ).choose_spec.2]
  rfl

theorem bc_injective (W : HSp D) {g g' : GL (Fin W.rank) D.host.E}
    (h : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) =
      (g' : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) : g = g' := by
  exact Units.ext (Matrix.ext fun i j => incA_injective D (congrFun (congrFun h i) j))

theorem graphSub_injective (W : HSp D) {c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (h : graphSub W c = graphSub W c') : c = c' := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hx : (x, c *ᵥ x) ∈ graphSub W c' := h ▸ mem_graphSub.2 rfl
  exact mem_graphSub.1 hx

theorem isLagFrame_graph (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    IsLagFrame W (graphLag W g hg) (1, (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E)) := by
  have h := congrArg (Submodule.map (LinearMap.prod (LinearMap.id : (Fin W.rank → D.host.E) →ₗ[D.host.E] _)
    (Matrix.mulVecLin (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E))))
    (Pi.basisFun D.host.E (Fin W.rank)).span_eq
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h
  refine Eq.trans ?_ h
  congr 2
  funext j
  ext a <;> simp [Matrix.one_apply, Pi.single_apply]

theorem hr_mem (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
      W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
  show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
      ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      W.gram.map (inclR (F := D.host.F) (AF D.host.F)) *
      (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) =
      W.gram.map (inclR (F := D.host.F) (AF D.host.F))
  rw [GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, h]

def ofRat (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : GQ W :=
  ⟨(⟨Formalism.UG.bc (incA D) g, hr_mem W g hg⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram),
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)⟩

end GlobalTheory.RawLift.Graphs

namespace GlobalTheory.RawLift.Graphs

open GlobalTheory.RawLift.Graphs

theorem graphs : ∀ (D : D7) (W : HSp D), ∃ e : GQ W ≃ {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥},
    ∀ γ : GQ W, ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W (γ : GA D W) = c.map (incA D) ∧ IsLagFrame W (e γ).1 (1, c) := by
  intro D W
  let f : GQ W → {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} :=
    fun γ => ⟨graphLag W (ratG W γ) (ratG_mem W γ), graphLag_bot W _ _⟩
  have hinj : Function.Injective f := by
    intro γ γ' h
    have h1 : graphSub W (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = graphSub W (ratG W γ') :=
      congrArg (fun Y => Y.1.1) h
    have h2 := graphSub_injective W h1
    have h3 : Formalism.L2.Theta.mt W (γ : GA D W) = Formalism.L2.Theta.mt W (γ' : GA D W) := by
      rw [mt_ratG, mt_ratG, h2]
    exact Subtype.ext (GlobalTheory.AutFunCounterexample.GA_ext W h3)
  have hsurj : Function.Surjective f := by
    rintro ⟨Y, hY⟩
    obtain ⟨g, hgU, hgY⟩ := ((GlobalTheory.Doubling.maximal_isotropic_doubled D.host.E starRingAut W.rank W.gram
      (fun x => star_star x) (GlobalTheory.AutFunCounterexample.gram_det_ne W) (herm' W) Y.1 Y.2.1 Y.2.2).2.2).1 hY
    have hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := hgU
    refine ⟨ofRat W g hg, Subtype.ext (Subtype.ext ?_)⟩
    have e1 : ratG W (ofRat W g hg) = g := bc_injective W ((mt_ratG W _).symm.trans rfl)
    show graphSub W (ratG W (ofRat W g hg)) = Y.1
    rw [e1]
    ext y
    rw [mem_graphSub]
    exact (hgY y).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun γ => ⟨_, mt_ratG W γ, isLagFrame_graph W _ (ratG_mem W γ)⟩⟩

end GlobalTheory.RawLift.Graphs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMulti
section
noncomputable section

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published

namespace GlobalTheory.LocGL

theorem hasSupport_msupp_of_isL (hZ : ZelevinskyPolynomialRing) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k))
    (h : IsL 𝔪 x.rep) : HasSupport x.rep (msupp 𝔪) := by

  obtain ⟨_, Ψ, -, hΨ, -⟩ := hZ k

  obtain ⟨c, y, hd, ⟨Δ, ⟨hΔ, -⟩, hy⟩, hx⟩ := h

  have key : HasSupport x.rep (∑ a, (Δ a).ms) :=
    SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ (fun a => (hy a).hasSupport) hx.1 hx.isSubquotient

  have e : msupp 𝔪 = ∑ a, (Δ a).ms := by
    rw [← hΔ, msupp, Multiset.bind, Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  rw [e]
  exact key

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsLStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) → (∀ (d h : ℕ) (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM'))) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V)
    (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
    ∀ (d n : ℕ) (hdn : ∑ _ : Fin d, a = n) (W : Type) [AddCommGroup W] [Module ℂ W]
      (σ' : Representation ℂ (GL (Fin n) k) W), σ'.IsIrreducible →
      (∃ f : (multiProd (stdBlocks (fun _ : Fin d => a) hdn) fun i : Fin d =>
        twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).IntertwiningMap σ',
        Function.Surjective f) →
      IsL ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) σ' := by
  first | exact @GlobalTheory.speh_quotient_isL | exact GlobalTheory.speh_quotient_isL | (intros; apply GlobalTheory.speh_quotient_isL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDSingleLeviEmbEqZero
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.UnipZero

theorem mem_unipRad_of_eq_one {R : Type} [CommRing R] {c N : ℕ} {n : Fin c → ℕ}
    {e : (Σ i, Fin (n i)) ≃ Fin N} {p q : Fin N} (hpq : blk e p < blk e q) (u : GL (Fin N) R)
    (hu : ∀ i j, ¬ (i = p ∧ j = q) → (u : Matrix (Fin N) (Fin N) R) i j = (1 : Matrix (Fin N) (Fin N) R) i j) :
    u ∈ unipRad R e := by
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : ¬ (i = p ∧ j = q) := by
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hij hpq
    rw [hu i j hne, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij
  · have hne : ¬ (e ⟨a, i⟩ = p ∧ e ⟨a, j⟩ = q) := by
      rintro ⟨h1, h2⟩
      have h1' : blk e p = a := by rw [← h1, blk_apply]
      have h2' : blk e q = a := by rw [← h2, blk_apply]
      rw [h1', h2'] at hpq
      exact lt_irrefl _ hpq
    rw [hu _ _ hne]
    simp [Matrix.one_apply, e.injective.eq_iff]

end GlobalTheory.UnipZero

namespace GlobalTheory.UnipZero

theorem lieD_single_leviEmb_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N) (ψ : Sm E N)
    (hψ : ∀ u ∈ unipRad (Ad E) e, ∀ g, ψ.1 (u * g) = ψ.1 g) (p q : Fin N) (hpq : blk e p < blk e q)
    (x : Cinf E) (m : ∀ i, GA E (n i)) :
    (lie E N (toL (Matrix.single p q x)) ψ).1 (leviEmb (Ad E) e m) = 0 := by
  set S : Matrix (Fin N) (Fin N) (Cinf E) := Matrix.single p q x with hS
  have hpq' : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
  have hSS : S * S = 0 := by rw [hS]; simp [hpq'.symm]
  let cc : ℝ → GL (Fin N) (Cinf E) := fun t =>
    ⟨1 + t • S, 1 - t • S, by
      rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel, by
      rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel⟩
  have h0 : cc 0 = 1 := Units.ext (by simp [cc])
  have hc : HasDerivAt (fun t => toL (cc t).val) (toL S) 0 := by
    have h : HasDerivAt (fun t : ℝ => toL (1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • toL S) ((1 : ℝ) • toL S) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const (toL S)).const_add _
    rw [one_smul] at h
    exact h
  set g := leviEmb (Ad E) e m
  have hmem : ∀ t, infGL E N (cc t) ∈ unipRad (Ad E) e := by
    intro t
    refine mem_unipRad_of_eq_one hpq _ fun i j hij => ?_
    have hij' : ((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j =
        (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j := by
      change ((1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • S) i j = _
      have h1 : S i j = 0 := by
        rw [hS, Matrix.single_apply_of_ne]
        exact fun h => hij ⟨h.1.symm, h.2.symm⟩
      rw [Matrix.add_apply, Matrix.smul_apply, h1, smul_zero, add_zero]
    change (1 : Matrix (Fin N) (Fin N) (Ad E)) i j - sInf E ((1 : Matrix (Fin N) (Fin N) (Cinf E)) i j) +
      sInf E (((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j) = _
    rw [hij', sub_add_cancel]
  have hconst : (fun t => ψ.1 (g * infGL E N (cc t))) = fun _ => ψ.1 g := by
    funext t
    have hconj : g * infGL E N (cc t) * g⁻¹ ∈ unipRad (Ad E) e :=
      (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 (hmem t)
    have := hψ _ hconj g
    rwa [inv_mul_cancel_right] at this
  have hd := hasDerivAt_curve ψ g cc (toL S) h0 hc
  rw [hconst] at hd
  rw [lie_apply]
  exact hd.unique (hasDerivAt_const _ _)

end GlobalTheory.UnipZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieMemCompactFiniteVectorsOfMem
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.LieFin

theorem lie_mem_finVec : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (X : Lie E N) (φ : Sm E N),
    φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) := by
  intro E _ _ _ N X φ hφ
  let S : Submodule ℂ (Sm E N) := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)
  haveI : FiniteDimensional ℂ S := hφ
  let b := Module.finBasis ℝ (Lie E N)
  let T : Submodule ℂ (Sm E N) := ⨆ s, S.map (lie E N (b s))
  haveI : FiniteDimensional ℂ T := by
    haveI : ∀ s, FiniteDimensional ℂ (S.map (lie E N (b s))) := fun s => inferInstance
    exact Submodule.finiteDimensional_iSup _
  have key : ∀ (Z : Lie E N) (ψ : Sm E N), ψ ∈ S → lie E N Z ψ ∈ T := by
    intro Z ψ hψ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr Z, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [map_smul, LinearMap.smul_apply]
    have h1 : lie E N (b s) ψ ∈ T :=
      (le_iSup (fun s => S.map (lie E N (b s))) s) (Submodule.mem_map_of_mem hψ)
    have h2 : ((b.repr Z s : ℝ) : ℂ) • lie E N (b s) ψ ∈ T := T.smul_mem _ h1
    simpa [Complex.coe_smul] using h2
  show FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k (lie E N X φ)))
  refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have e := congrArg (fun f : Module.End ℂ (Sm E N) => f φ) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  simp only [Module.End.mul_apply] at e
  change rt E N (infGL E N (Unitary.toUnits k)) (lie E N X φ) ∈ T
  have eX : toL (Matrix.of X) = X := rfl
  rw [eX] at e
  rw [e]
  exact key _ _ (Submodule.subset_span ⟨k, rfl⟩)

end GlobalTheory.LieFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisConvIffInnerProduct
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.RawLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cmp.RallisRange

variable {D : D7} {V W : HSp D}

theorem vol_lt_top (V : HSp D) {ν : Measure (GA D V)} {𝓗 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h : IsFundamentalDomain (GQ V) 𝓗 ν) : ν 𝓗 < ⊤ :=
  GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓗 hν h

end GlobalTheory.Cmp.RallisRange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatSubst

theorem om_rat_left_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ x, ω (γ, 1) f x = f (actO S T γ⁻¹ 1 x) := by
  intro D ψ S T χS χT ω hω f hf γ hγ x
  have h := GlobalTheory.SiegelFormula.om_rat_apply hω hγ (one_mem (GQ T)) (actO S T γ⁻¹ 1 x) hf
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hω.std hf _)
  have e : actO S T γ 1 (actO S T γ⁻¹ 1 x) = x := by
    have h1 : Formalism.L2.Theta.mt T 1 = 1 := rfl
    have h2 : Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ = 1 := by
      have : Formalism.L2.Theta.mt S (γ * γ⁻¹) = Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ := rfl
      rw [← this, mul_inv_cancel]; rfl
    unfold actO
    rw [inv_inv, h1, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  rwa [e] at h

end GlobalTheory.RatSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RawLiftOntoOfUpInj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory


set_option maxHeartbeats 1000000 in
theorem rawLift_onto_of_upInj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RatSpan R → (∀ i, UpInj R i A.μ0) → ThOnto R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hS hU i
  obtain ⟨th, hth⟩ := hL.exists_isRaw i A.μ0
  have hsurj := (GlobalTheory.adjoint_injective_surjective_and_positive_scalar _ _ th).1 (hU i th hth)
  rw [hS i A.μ0, Submodule.map_top]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact hL.thP.thF_mem i A.μ0 x
  · intro w hw
    rw [← (hL.models.HW i (sg0 D A)).2.1] at hw
    obtain ⟨y, rfl⟩ := hw
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, (hth x).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehLanglandsQuotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.speh_langlands_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (δ x : IrrGL (k := k)) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep := by
  first | exact @GlobalTheory.LocGL.isL_speh_nu | exact GlobalTheory.LocGL.isL_speh_nu | (intros; apply GlobalTheory.LocGL.isL_speh_nu <;> assumption)
end

