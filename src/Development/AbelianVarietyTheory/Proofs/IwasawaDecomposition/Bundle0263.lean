module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0121

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdBlockSymbolDetPow
section
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.BlockTop

section General

variable {α : Type} [Fintype α] [DecidableEq α]

def graph (w : Equiv.Perm α) : α × α →₀ ℕ := ∑ a, Finsupp.single (a, w a) 1

def tc (P : MvPolynomial (α × α) ℂ) : ℂ :=
  ∑ w : Equiv.Perm α, ((Equiv.Perm.sign w : ℤ) : ℂ) * AddMonoidAlgebra.coeff P (graph w)

theorem topCoeff_eq_tc {n : ℕ} (P : MvPolynomial (Fin n × Fin n) ℂ) : GlobalTheory.GoodMetric.topCoeff P = tc P := rfl

theorem tc_sum {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (α × α) ℂ) :
    tc (∑ i ∈ s, f i) = ∑ i ∈ s, tc (f i) := by
  simp only [tc, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem tc_monomial (u : α × α →₀ ℕ) (c : ℂ) : tc (monomial u c) = c * tc (monomial u 1) := by
  simp only [tc, coeff_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

theorem graph_apply (w : Equiv.Perm α) (a b : α) : graph w (a, b) = if w a = b then 1 else 0 := by
  rw [graph, Finsupp.finsetSum_apply, Finset.sum_eq_single a (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem tc_rename_equiv {β : Type} [Fintype β] [DecidableEq β] (e : α ≃ β) (P : MvPolynomial (α × α) ℂ) :
    tc (rename (Prod.map e e) P) = tc P := by
  unfold tc
  rw [← (Equiv.permCongr e).sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hg : graph (e.permCongr v) = Finsupp.mapDomain (Prod.map e e) (graph v) := by
    unfold graph
    rw [Finsupp.mapDomain_finsetSum]
    simp only [Finsupp.mapDomain_single]
    rw [← e.sum_comp]
    simp [Equiv.permCongr_apply]
  have hinj : Function.Injective (Prod.map e e) := fun x y h => by
    simp only [Prod.map, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact Prod.ext h.1 h.2
  rw [hg, coeff_rename_mapDomain _ hinj, Equiv.Perm.sign_permCongr]

theorem prod_monomial' {κ : Type} (s : Finset κ) (f : κ → α × α →₀ ℕ) (c : κ → ℂ) :
    ∏ i ∈ s, (monomial (f i) (c i) : MvPolynomial (α × α) ℂ) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, ih, monomial_mul, Finset.sum_insert ha, Finset.prod_insert ha]

end General

section Blocks

variable {ι γ : Type} [Fintype ι] [DecidableEq ι] [Fintype γ] [DecidableEq γ]

def emb (τ : ι) (v : γ × γ) : (ι × γ) × (ι × γ) := ((τ, v.1), (τ, v.2))

theorem emb_injective (τ : ι) : Function.Injective (emb (γ := γ) τ) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [emb, Prod.mk.injEq, true_and] at h
  simp [h]

def glue (D : ι → (γ × γ →₀ ℕ)) : (ι × γ) × (ι × γ) →₀ ℕ := ∑ τ, (D τ).mapDomain (emb τ)

theorem glue_emb (D : ι → (γ × γ →₀ ℕ)) (τ : ι) (v : γ × γ) : glue D (emb τ v) = D τ v := by
  unfold glue
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply_of_injective (emb_injective τ) _ _
  · intro τ' _ hτ'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨u, hu⟩
    simp only [emb, Prod.mk.injEq] at hu
    exact hτ' hu.1.1
  · simp

theorem glue_off (D : ι → (γ × γ →₀ ℕ)) (a b : ι × γ) (h : a.1 ≠ b.1) : glue D (a, b) = 0 := by
  unfold glue
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun τ _ => Finsupp.mapDomain_notin_range _ _ ?_
  rintro ⟨u, hu⟩
  simp only [emb, Prod.mk.injEq] at hu
  exact h (by rw [← hu.1, ← hu.2])

theorem glue_injective : Function.Injective (glue (ι := ι) (γ := γ)) := by
  intro D D' h
  funext τ
  ext v
  rw [← glue_emb, h, glue_emb]

theorem graph_prodCongrRight (σ : ι → Equiv.Perm γ) :
    graph (Equiv.prodCongrRight σ) = glue fun τ => graph (σ τ) := by
  unfold glue graph
  simp only [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
  rw [Fintype.sum_prod_type]
  simp only [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, emb, Equiv.prodCongrRight_apply]

theorem exists_prodCongrRight (w : Equiv.Perm (ι × γ)) (hw : ∀ a, (w a).1 = a.1) :
    ∃ σ : ι → Equiv.Perm γ, Equiv.prodCongrRight σ = w := by
  have hw' : ∀ b, (w.symm b).1 = b.1 := fun b => by
    have := hw (w.symm b)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have li : ∀ τ x, (w.symm (τ, (w (τ, x)).2)).2 = x := fun τ x => by
    have e1 : (τ, (w (τ, x)).2) = w (τ, x) := Prod.ext (hw (τ, x)).symm rfl
    rw [e1, Equiv.symm_apply_apply]
  have ri : ∀ τ x, (w (τ, (w.symm (τ, x)).2)).2 = x := fun τ x => by
    have e1 : (τ, (w.symm (τ, x)).2) = w.symm (τ, x) := Prod.ext (hw' (τ, x)).symm rfl
    rw [e1, Equiv.apply_symm_apply]
  refine ⟨fun τ => Equiv.mk (fun x => (w (τ, x)).2) (fun x => (w.symm (τ, x)).2) (li τ) (ri τ), ?_⟩
  ext ⟨τ, x⟩
  · simp [hw]
  · simp

theorem prodCongrRight_injective :
    Function.Injective (fun σ : ι → Equiv.Perm γ => (Equiv.prodCongrRight σ : Equiv.Perm (ι × γ))) := by
  intro σ σ' h
  funext τ
  ext x
  have := congrArg (fun w : Equiv.Perm (ι × γ) => (w (τ, x)).2) h
  simpa using this

theorem tc_monomial_glue (D : ι → (γ × γ →₀ ℕ)) :
    tc (monomial (glue D) (1 : ℂ)) = ∏ τ, tc (monomial (D τ) (1 : ℂ)) := by
  simp only [tc, coeff_monomial]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  set F : Equiv.Perm (ι × γ) → ℂ := fun w => ((Equiv.Perm.sign w : ℤ) : ℂ) * if glue D = graph w then 1 else 0 with hF
  have h1 : ∑ w, F w = ∑ w ∈ Finset.univ.image (fun σ : ι → Equiv.Perm γ => Equiv.prodCongrRight σ), F w := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun w _ hw => ?_).symm
    simp only [hF]
    rw [if_neg, mul_zero]
    intro hg
    apply hw
    have hb : ∀ a, (w a).1 = a.1 := by
      intro a
      by_contra hne
      have e1 := glue_off D a (w a) (Ne.symm hne)
      rw [hg, graph_apply, if_pos rfl] at e1
      exact one_ne_zero e1
    obtain ⟨σ, hσ⟩ := exists_prodCongrRight w hb
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩
  rw [h1, Finset.sum_image fun x _ y _ h => prodCongrRight_injective h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [hF, graph_prodCongrRight, glue_injective.eq_iff, Equiv.Perm.sign_prodCongrRight]
  rw [Finset.prod_mul_distrib]
  push_cast
  congr 1
  by_cases hD : D = fun τ => graph (σ τ)
  · rw [if_pos hD]
    symm
    exact Finset.prod_eq_one fun τ _ => if_pos (congrFun hD τ)
  · rw [if_neg hD]
    obtain ⟨τ, hτ⟩ : ∃ τ, D τ ≠ graph (σ τ) := by
      by_contra hall
      push_neg at hall
      exact hD (funext hall)
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)

theorem tc_prod_rename (f : ι → MvPolynomial (γ × γ) ℂ) :
    tc (∏ τ, rename (emb τ) (f τ)) = ∏ τ, tc (f τ) := by
  have hL : ∏ τ, rename (emb τ) (f τ) = ∑ x ∈ Fintype.piFinset fun τ => (f τ).support,
      monomial (glue x) (∏ τ, AddMonoidAlgebra.coeff (f τ) (x τ)) := by
    calc ∏ τ, rename (emb τ) (f τ)
        = ∏ τ, ∑ d ∈ (f τ).support, monomial (d.mapDomain (emb τ)) (AddMonoidAlgebra.coeff (f τ) d) := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          conv_lhs => rw [(f τ).as_sum]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          simp only [rename_monomial]
      _ = _ := by
          rw [Finset.prod_univ_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [prod_monomial']
          rfl
  have hR : ∀ τ, tc (f τ) = ∑ d ∈ (f τ).support, AddMonoidAlgebra.coeff (f τ) d * tc (monomial d (1 : ℂ)) := by
    intro τ
    conv_lhs => rw [(f τ).as_sum]
    rw [tc_sum]
    exact Finset.sum_congr rfl fun d _ => tc_monomial _ _
  rw [hL, tc_sum]
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tc_monomial, tc_monomial_glue, Finset.prod_mul_distrib]

end Blocks

end GlobalTheory.BlockTop

namespace GlobalTheory.BlockTop

def symMat (p q : ℕ) : Matrix (Fin p) (Fin p) (MvPolynomial ((Fin p × Fin q) × (Fin p × Fin q)) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q, X ((i, b), (j, b))

theorem det_map_rename {σ' : Type} (p q : ℕ) (g : (Fin p × Fin q) × (Fin p × Fin q) → σ') :
    ((symMat p q).map (rename (R := ℂ) g)).det = rename g (symMat p q).det :=
  (AlgHom.map_det (rename g) _).symm

theorem blockSym_eq {ι : Type} [Fintype ι] {p q n : ℕ} (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    GlobalTheory.DomainDens.blockSym h τ = (symMat p q).map
      (rename (Prod.map (Fintype.equivFinOfCardEq h) (Fintype.equivFinOfCardEq h) ∘ emb τ)) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.DomainDens.blockSym, symMat, map_sum, rename_X, emb]

end GlobalTheory.BlockTop


open GlobalTheory.BlockTop in
theorem GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow : ∀ (ι : Type) [Fintype ι] (p q n : ℕ)
    (h : Fintype.card (ι × Fin p × Fin q) = n) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q),
    GlobalTheory.GoodMetric.topCoeff (∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q) =
      GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) ^ Fintype.card ι := by
  intro ι _ p q n h h1
  classical
  set e := Fintype.equivFinOfCardEq h
  set e1 := Fintype.equivFinOfCardEq h1
  have hL : ∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q =
      rename (Prod.map e e) (∏ τ, rename (emb τ) ((symMat p q).det ^ q)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [blockSym_eq, det_map_rename, rename_rename, map_pow]
  set e' : Fin p × Fin q ≃ Fin (p * q) := (Equiv.punitProd (Fin p × Fin q)).symm.trans e1
  have hR : (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (Prod.map e' e') ((symMat p q).det ^ q) := by
    rw [blockSym_eq, det_map_rename, map_pow]
    rfl
  rw [hL, hR, topCoeff_eq_tc, topCoeff_eq_tc, tc_rename_equiv, tc_rename_equiv, tc_prod_rename,
    Finset.prod_const, Finset.card_univ]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingSchurOrthogonalityDefiniteCoefficients
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.SchurW


set_option maxHeartbeats 8000000 in
theorem schurW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (t : T) (h h' : (R.HX t).H) (a a' : R.cX.W), IntegrableOn (fun g => star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ) (R.fdX t) (R.νX t) ∧ (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ ∂(R.νX t) = ⟪a', a⟫_ℂ * ⟪h, h'⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB t h h' a a'
  haveI : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D D.sp.X') := ⟨rfl⟩
  haveI : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram
  have hμ := hB.models.νX t
  haveI := hμ.1.1
  have hc := hB.models.cX
  have hH := hB.models.HX t
  let J := (levEnv D.sp.X' R.βX (R.datXt t)).J
  let χ := (levEnv D.sp.X' R.βX (R.datXt t)).χ
  let Ω : Subgroup (GA D D.sp.X') := (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)).comap (finE D.sp.X')
  have hK : ∀ g : GA D D.sp.X', g ∈ Ω ↔ (finHom D.sp.X').rangeRestrict g ∈ J := fun g => Iff.rfl
  have hΩo : IsOpen (Ω : Set (GA D D.sp.X')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level D.sp.X' R.βX (R.datXt t)] with κ hκ
    exact (hK κ).2 hκ.1
  have hΩ1 : R.νX t (Ω : Set (GA D D.sp.X')) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  have hF : ∀ x, (R.HX t).e x ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ := fun x => by
    have := LinearMap.mem_range_self (R.HX t).e x
    rw [hH.2.1] at this
    exact this
  have hinv : ∀ (u : GA D D.sp.X') v, R.cX.ρ u⁻¹ (R.cX.ρ u v) = v := fun u v => by
    have := congrArg (fun T : Module.End ℂ R.cX.W => T v) (show R.cX.ρ u⁻¹ * R.cX.ρ u = 1 by rw [← map_mul, inv_mul_cancel, map_one])
    exact this
  have hext : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ (γ : GA D D.sp.X'), γ ∈ GQ D.sp.X' →
      ∀ g, R.cX.ext f (γ * g) = R.cX.ext f g := by
    intro f hf γ hγ g
    show R.cX.ρ (γ * g)⁻¹ (f ((finHom D.sp.X').rangeRestrict (γ * g))) = R.cX.ρ g⁻¹ (f ((finHom D.sp.X').rangeRestrict g))
    have := hf ⟨γ, hγ⟩ ((finHom D.sp.X').rangeRestrict g) 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this
    rw [map_mul]
    erw [this]
    show R.cX.ρ (γ * g)⁻¹ (R.cX.ρ γ _) = _
    rw [_root_.mul_inv_rev, map_mul]
    exact congrArg (R.cX.ρ g⁻¹) (hinv γ _)
  choose y' hy'1 hy'2 using fun c => GlobalTheory.DefiniteMult.exists_fin_lift D.sp.X' ((R.B.R t).pres.y c)
  have hnorm : ∀ k : J, ‖((χ k : ℂˣ) : ℂ)‖ = 1 := fun k => GlobalTheory.AdelicScalar.norm_levFn _ _ _
  have hloc : ∀ f, f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ J χ → ∀ c, ∀ k (hk : k ∈ Ω),
      R.cX.ext f (y' c * k) = ((χ ⟨_, (hK k).1 hk⟩ : ℂˣ) : ℂ) • R.cX.ρ k⁻¹ (f ((R.B.R t).pres.y c)) := by
    intro f hf c k hk
    have e1 : (finHom D.sp.X').rangeRestrict (y' c * k) = (R.B.R t).pres.y c * (finHom D.sp.X').rangeRestrict k := by
      rw [MonoidHom.map_mul, hy'2]
    have e2 := GlobalTheory.DefiniteMult.adForms_level hf ((R.B.R t).pres.y c) ⟨_, (hK k).1 hk⟩
    have e3 : R.cX.ρ (y' c * k)⁻¹ = R.cX.ρ k⁻¹ := by
      rw [_root_.mul_inv_rev, map_mul, hc.1 _ (inv_mem (hy'1 c)), mul_one]
    show R.cX.ρ (y' c * k)⁻¹ (f ((finHom D.sp.X').rangeRestrict (y' c * k))) = _
    refine (congrArg (R.cX.ρ (y' c * k)⁻¹) ((congrArg f e1).trans e2)).trans ?_
    refine (map_smul _ _ _).trans ?_
    exact congrArg (_ • ·) (LinearMap.congr_fun e3 _)
  let φ : GA D D.sp.X' → ℂ := fun g =>
    star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ
  have hpt : ∀ c, ∀ k ∈ Ω, φ (y' c * k) = star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ *
      ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ := by
    intro c k hk
    have key : ∀ z p q : ℂ, ‖z‖ = 1 → star (z * p) * (z * q) = star p * q := by
      intro z p q hz
      have e : star z * z = 1 := by
        rw [Complex.star_def, Complex.conj_mul', hz]; norm_num
      rw [star_mul']
      linear_combination (star p * q) * e
    have hz := hnorm ⟨_, (hK k).1 hk⟩
    refine (congrArg₂ (fun u v : ℂ => star u * v) (congrArg (inner ℂ a) (hloc _ (hF h) c k hk))
      (congrArg (inner ℂ a') (hloc _ (hF h') c k hk))).trans ?_
    simp only [inner_smul_right]
    exact key _ _ _ hz
  have hmeas : ∀ x y : R.cX.W, Measurable fun g => ⟪x, R.cX.ρ g y⟫_ℂ := fun x y =>
    (continuous_const.inner (hc.2.2.1 y)).measurable
  have hirr : ∀ U : Submodule ℂ R.cX.W, (∀ g ∈ Ω, U.map (R.cX.ρ g) ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hc.2.2.2.2 U fun g => ?_
    obtain ⟨a0, ha0, k0, hk0, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D D.sp.X').1 g
    rw [map_mul, hc.1 k0 hk0, mul_one]
    refine hU a0 ((hK a0).2 ?_)
    have e : (finHom D.sp.X').rangeRestrict a0 = 1 := Subtype.ext ha0
    exact e ▸ J.one_mem
  have hS := fun c => GlobalTheory.T.schur_orthogonality_subgroup_measure_one (R.νX t) Ω hΩo.measurableSet hΩ1 R.cX.ρ hc.2.1 hmeas hirr a a'
    ((R.HX t).e h ((R.B.R t).pres.y c)) ((R.HX t).e h' ((R.B.R t).pres.y c))
  have huniq : ∀ x : GA D D.sp.X', ∃! i, ∃ γ ∈ GQ D.sp.X', ∃ k ∈ Ω, x = γ * y' i * k := by
    intro x
    refine (existsUnique_congr fun i => ?_).1 ((R.B.R t).pres.reps ((finHom D.sp.X').rangeRestrict x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, (γ * y' i)⁻¹ * x, (hK _).2 ?_, by group⟩
      have e' : (finHom D.sp.X').rangeRestrict ((γ * y' i)⁻¹ * x) = k := by
        simp only [map_mul, map_inv, hy'2, e]
        change (Bridge.ratF D.sp.X' γ * _)⁻¹ * (Bridge.ratF D.sp.X' γ * _ * k) = _
        exact inv_mul_cancel_left _ _
      exact cast (congrArg (· ∈ J) e').symm k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨⟨γ, hγ⟩, ⟨_, (hK k).1 hk⟩, ?_⟩
      simp only [map_mul, hy'2]
      rfl
  have hSet : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω} =
      Subtype.val '' (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c) : Set (GQ D.sp.X')) := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨γ, h1⟩, ?_, rfl⟩
      have := (hK _).1 h2
      simp only [map_mul, map_inv, hy'2] at this
      exact this
    · rintro ⟨δ, h2, rfl⟩
      refine ⟨δ.2, (hK _).2 ?_⟩
      simp only [map_mul, map_inv, hy'2]
      exact h2
  have hfinS : ∀ c, Finite (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) := fun c =>
    Finite.of_equiv _ ((R.B.R t).pres.stabI c).toEquiv
  have hfin : ∀ c, {γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.Finite := fun c => by
    rw [hSet]
    haveI := hfinS c
    exact (Set.toFinite _).image _
  have hcard : ∀ c, ({γ : GA D D.sp.X' | γ ∈ GQ D.sp.X' ∧ (y' c)⁻¹ * γ * y' c ∈ Ω}.ncard : ℂ) =
      (Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ) := fun c => by
    have e := congrArg Set.ncard (hSet c)
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at e
    exact (congrArg (Nat.cast : ℕ → ℂ) e).trans (congrArg (Nat.cast : ℕ → ℂ) (Nat.card_coe_set_eq _).symm)
  have hintc : ∀ c, IntegrableOn (fun k => φ (y' c * k)) Ω (R.νX t) := fun c =>
    (hS c).1.congr_fun (fun k hk => (hpt c k hk).symm) hΩo.measurableSet
  have hIc : ∀ c, ∫ k in (Ω : Set (GA D D.sp.X')), φ (y' c * k) ∂(R.νX t) =
      ∫ k in (Ω : Set (GA D D.sp.X')), star ⟪a, R.cX.ρ k⁻¹ ((R.HX t).e h ((R.B.R t).pres.y c))⟫_ℂ *
        ⟪a', R.cX.ρ k⁻¹ ((R.HX t).e h' ((R.B.R t).pres.y c))⟫_ℂ ∂(R.νX t) := fun c =>
    setIntegral_congr_fun hΩo.measurableSet fun k hk => hpt c k hk
  have hfl : ∀ γ : GA D D.sp.X', γ ∈ GQ D.sp.X' → ∀ x : GA D D.sp.X', φ (γ * x) = φ x := fun γ hγ x => by
    show star ⟪a, R.cX.ext ((R.HX t).e h) (γ * x)⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') (γ * x)⟫_ℂ =
      star ⟪a, R.cX.ext ((R.HX t).e h) x⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') x⟫_ℂ
    exact congrArg₂ (fun u v => star ⟪a, u⟫_ℂ * ⟪a', v⟫_ℂ) (hext _ (hF h) γ hγ x) (hext _ (hF h') γ hγ x)
  have U1 := _root_.GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold (GA D D.sp.X') (R.νX t) (GQ D.sp.X') Ω (R.fdX t) hμ.2 hΩo _ y' huniq hfin φ hfl hintc
  refine ⟨U1.1, ?_⟩
  change (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, φ g ∂(R.νX t) = _
  refine (congrArg (_ * ·) U1.2).trans ?_
  refine Eq.trans ?_ (congrArg (⟪a', a⟫_ℂ * ·) (hH.2.2 h h').symm)
  simp only [Bridge.adInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine (congrArg₂ (fun (u v : ℂ) => (Module.finrank ℂ R.cX.W : ℂ) * (u⁻¹ * v)) (hcard c) (hIc c)).trans ?_
  linear_combination ((Nat.card (Bridge.stab (Bridge.ratF D.sp.X') J ((R.B.R t).pres.y c)) : ℂ)⁻¹) * (hS c).2

end GlobalTheory.Mem.SchurW
end

