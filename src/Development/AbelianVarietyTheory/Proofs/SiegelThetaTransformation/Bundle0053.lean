module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorOriginEqPolyDeriv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockOrigin

theorem prod_C_mul_X {σ σ' : Type} [DecidableEq σ'] (c : σ → ℂ) (f : σ → σ') (L : List σ) :
    (L.map fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)).prod =
      (L.map c).prod • MvPolynomial.monomial (Multiset.toFinsupp ((L.map f : List σ') : Multiset σ')) (1 : ℂ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons,
      ← Multiset.cons_coe, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton,
      MvPolynomial.X, MvPolynomial.C_mul', smul_mul_smul_comm, MvPolynomial.monomial_mul, one_mul]

theorem polyDeriv_aeval_monomial {σ σ' W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (c : σ → ℂ) (f : σ → σ') (u : σ' → W) {θ : W → ℂ} (hθ : ContDiff ℂ (⊤ : ℕ∞) θ) (m : σ →₀ ℕ) (x : W) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v))
      (MvPolynomial.monomial m (1 : ℂ))) u θ x =
      ((Finsupp.toMultiset m).toList.map c).prod *
        I2.itD θ ((Finsupp.toMultiset m).toList.map fun v => u (f v)) x := by
  have h1 := prod_C_mul_X (fun _ : σ => (1 : ℂ)) id (Finsupp.toMultiset m).toList
  simp only [map_one, one_mul, id, List.map_id, List.map_const',
    List.prod_replicate, one_pow, one_smul, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp] at h1
  rw [← h1, map_list_prod, List.map_map]
  have h2 : (⇑(MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)) :
      MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ) ∘ fun v => MvPolynomial.X v) =
      fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v) := by
    funext v; simp
  rw [h2, prod_C_mul_X, I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
    Multiset.toFinsupp_toMultiset]
  congr 1
  refine congrFun (I2.ct_itD_perm hθ ?_) x
  have h3 : ((Finsupp.toMultiset m).toList.map fun v => u (f v)) =
      ((Finsupp.toMultiset m).toList.map f).map u := by rw [List.map_map]; rfl
  rw [h3]
  refine List.Perm.map u ?_
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]

theorem fvec_zero_eq_polyDeriv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (θ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℂ θ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * θ (C.zOf (C.xB B) w)) → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B G Q 0 = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (C.toH Q) (letterDir C.X C.hr C.idx) θ 0 := by
  intro D S T C B hB G θ hθ hG Q
  obtain ⟨R, -, -, hadd, -⟩ := GlobalTheory.KerReal.real_points D S T C
  obtain ⟨-, -, -, -, hdir, -⟩ := (_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  set x := C.xB B with hx0
  let f : FVar D T.rank S.rank → Harm.Var C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
    fun v => (C.m.e v.1, (rowIdx C.hr).symm v.2.1, v.2.2)
  let c : FVar D T.rank S.rank → ℂ := fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)
  let u : FVar D T.rank S.rank → Fin S.rank → Fin C.g → ℂ := fun v => letterDir C.X C.hr C.idx (f v)
  let lam : FVar D T.rank S.rank → (Fin S.rank → Fin C.g → ℂ) → ℂ := fun v z =>
    -(π * ∑ k, hx C.X C.bas C.idx x (u v k) (z k))
  let Dl : FVar D T.rank S.rank → ((Fin S.rank → Fin C.g → ℂ) → ℂ) → (Fin S.rank → Fin C.g → ℂ) → ℂ :=
    fun l Φ z => lam l z * Φ z + (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))
  have hlam : ∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a := by
    intro l
    refine ⟨fun a b => ?_, fun t a => ?_⟩
    · simp only [lam, GlobalTheory.Dict.hx, Pi.add_apply, mulVec_add, star_add, dotProduct_add,
        Finset.sum_add_distrib]
      ring
    · simp only [lam, GlobalTheory.Dict.hx, Pi.smul_apply, mulVec_smul, star_smul, dotProduct_smul,
        smul_eq_mul, ← Finset.mul_sum, RCLike.star_def]
      ring
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u lam θ hlam hθ Dl (fun _ _ _ => rfl)
  let A := aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B
  have key : ∀ L : List (FVar D T.rank S.rank), ∀ w, IsRealPt w →
      L.foldr (fun i g => A i g) G w =
        gaussR C.X C.bas C.idx x (C.zOf x w) * ((L.map c).prod * L.foldr Dl θ (C.zOf x w)) := by
    intro L
    induction L with
    | nil => intro w hw; simpa using hG w hw
    | cons a L ih =>
      intro w hw
      have hd : Differentiable ℝ (L.foldr Dl θ) := (hops L).1.differentiable (by simp)
      have h := (_root_.GlobalTheory.Ker.annih_crea_coord D S T C B hB _ (fun z => (L.map c).prod * L.foldr Dl θ z)
        (hd.const_mul _) ih a.1 (unitMap 1 (B a.1) a.2.1 a.2.2) (u a) (hdir a.1 a.2.1 a.2.2).symm w hw).2
      rw [List.foldr_cons]
      change ((fockScale D a.1 : ℂ)⁻¹) * crea (heisO C.ψ S T) C.θ a.1 (cplxO 1 (C.sB B a.1))
        (unitMap 1 (B a.1) a.2.1 a.2.2) (L.foldr (fun i g => A i g) G) w = _
      rw [h, fderiv_const_mul (hd _)]
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, _root_.smul_apply, smul_eq_mul]
      simp only [Dl, lam, c, ← hx0]
      push_cast
      ring
  have h0 : C.zOf x 0 = 0 := by
    have h1 : C.realPt 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    funext k i
    simp only [Ctx.zOf, h1, zR, Pi.zero_apply, mulVec_zero]
    split_ifs
    · simp [hermC]
    · rfl
  have hr0 : IsRealPt (0 : WO S T) := by
    unfold IsRealPt
    ext i j
    simp
  have hg0 : gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
    simp [gaussR, GlobalTheory.Dict.hx]
  have hsm := I2.contDiff_of_diff hθ
  induction Q using MvPolynomial.induction_on' with
  | add P P' hP hP' =>
    rw [map_add (f := _), I2.polyDeriv_add, ← hP, ← hP', Ctx.fvec, map_add (f := _)]
    rfl
  | monomial m a =>
    have e : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, I2.polyDeriv_smul, Ctx.fvec, map_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    have h2 : pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B G
        (MvPolynomial.monomial m (1 : ℂ)) = opPow A m G := by
      have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
        (fun k => opPow A k G) m
      rwa [MvPolynomial.coe_basisMonomials] at this
    rw [h2, opPow, key _ 0 hr0, h0, hg0, one_mul, (hops _).2]
    refine Eq.trans ?_ (polyDeriv_aeval_monomial c f _ hsm m 0).symm
    congr 1
    rw [I2.ct_iter_eq_itD_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map _ u

end GlobalTheory.Ker.FockOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSpace

open GlobalTheory.WeilVacMove

variable {D : D7} {S T : HSp D}

theorem stdL_full (E : Type) [Field E] [NumberField E] (r : ℕ) :
    (stdL E r).FG ∧ Submodule.span E (stdL E r : Set (Fin r → E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

theorem map_sub_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a b : A} (ha : φ a = 0) (hb : φ b = 0) :
    φ (a - b) = 0 := by rw [map_sub, ha, hb, sub_zero]

theorem map_nsmul_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a : A} (ha : φ a = 0) (N : ℕ) :
    φ (N • a) = 0 := by rw [map_nsmul, ha, smul_zero]

theorem isRealPt_sub {u v : WO S T} (hu : IsRealPt u) (hv : IsRealPt v) : IsRealPt (u - v) := by
  ext i j
  have h1 : finPart D (u i j) = 0 := congrFun (congrFun hu i) j
  have h2 : finPart D (v i j) = 0 := congrFun (congrFun hv i) j
  exact map_sub_eq_zero (finPart D) h1 h2

theorem isFinPt_nsmul {u : WO S T} (hu : IsFinPt u) (N : ℕ) : IsFinPt (N • u) := by
  ext i j
  have h1 : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  exact map_nsmul_eq_zero (infPart D) h1 N

theorem exists_fin_add_real (C : Ctx S T) (w : WO S T) : ∃ u v, IsFinPt u ∧ IsRealPt v ∧ w = u + v := by
  obtain ⟨R, -, -, -, h1, -, h2, -⟩ := _root_.GlobalTheory.KerReal.real_points D S T C
  exact ⟨_, _, h2 w, (h1 _).1, (sub_add_cancel _ _).symm⟩

theorem isTh_rho (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (w : WO S T) : C.IsTh (C.rho w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  have hfin {a : WO S T} (ha : IsFinPt a) {g : WO S T → ℂ} (hg : C.IsTh g) : C.IsTh (C.rho a g) := {
    quasi := heisO_quasi C.ψ S T a g hg.quasi
    level := by
      obtain ⟨U, hU, h1⟩ := hg.level
      refine ⟨U ⊓ GlobalTheory.FinTranslate.annSub C.ψ S T a, hU.inter (GlobalTheory.FinTranslate.isOpen_annSub C.std.1 ha), fun u hu h0 => ?_⟩
      have h2 : C.ψ (symplOH S T u a) = 1 ∧ C.ψ (symplOH S T a u) = 1 := hu.2
      conv_rhs => rw [← h1 u hu.1 h0]
      unfold Ctx.rho
      rw [heisO_heisO, heisO_heisO, h2.1, h2.2, add_comm]
    cont := by
      haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
      haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
      exact (C.std.1.1.comp (continuous_symplOH S T continuous_id continuous_const)).mul
        (hg.cont.comp (continuous_id.add continuous_const))
    smooth k L h1 h2 w := by
      have e : (fun t => heisO C.ψ S T a g (w + L t)) = fun t => C.ψ (symplOH S T w a) * g (w + a + L t) := by
        funext t
        rw [heisO, symplOH_add_left, (symplOH_fin_real S T a (L t) ha (h2 t)).2, add_zero, add_right_comm]
      rw [e]
      exact contDiff_const.mul (hg.smooth k L h1 h2 (w + a)) }
  have h := hfin hu (isTheta_heisO_real C.std hv hf)
  unfold Ctx.rho at h ⊢
  rwa [heisO_heisO, (symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one, one_smul] at h

theorem exists_level (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  obtain ⟨-, -, h3, h4, -⟩ := _root_.GlobalTheory.Ker.HatLat.hatA_tens D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := h4 U hU
  exact ⟨N, hN, fun u hu => h _ (hNU u hu) (isFinPt_nsmul (h3 u hu).1 N)⟩

theorem eq_zero_of_real (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (h0 : ∀ w, IsRealPt w → f w = 0) :
    f = 0 := by
  obtain ⟨h1, -, h3, -⟩ := _root_.GlobalTheory.Ker.HatLat.hatA_tens D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have h7 := (_root_.GlobalTheory.FormMatch.forms_match D S T C).2.2.2.2.2.2.2
  obtain ⟨N, hN, hl⟩ := exists_level C hf
  funext w
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  obtain ⟨y, hy⟩ := h1 u hu
  obtain ⟨-, hy2⟩ := h3 _ hy
  obtain ⟨y', -, u', hu', e⟩ := hy2 N hN
  have hr := isRealPt_sub hv (h7 (y + y')).2.2.1
  have e1 : u + v = ratW T S (y + y')ᵀ + ((v - (ratW T S (y + y')ᵀ - finW S T (y + y'))) + N • u') := by
    rw [(h7 y).2.2.2 y', sub_eq_iff_eq_add.1 e]
    abel
  have e2 := congrFun (hl u' hu') (v - (ratW T S (y + y')ᵀ - finW S T (y + y')))
  rw [h0 _ hr] at e2
  unfold Ctx.rho heisO at e2
  rw [(symplOH_fin_real S T _ _ (isFinPt_nsmul (h3 u' hu').1 N) hr).2, AddChar.map_zero_eq_one, one_mul] at e2
  rw [e1, hf.quasi, e2, mul_zero, Pi.zero_apply]

theorem rho_finW (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
    (w : WO S T) (hw : IsRealPt w) : C.rho (finW S T y) f w =
      cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y)) := by
  obtain ⟨-, h2, -, -, -, -, -, h7⟩ := _root_.GlobalTheory.FormMatch.forms_match D S T C
  obtain ⟨-, -, -, hadd, -, -, -, hfin, -⟩ := _root_.GlobalTheory.KerReal.real_points D S T C
  obtain ⟨a1, a2, a3, -⟩ := h7 y
  set z := ratW T S yᵀ - finW S T y with hz
  have hr : ratW T S yᵀ = finW S T y + z := by rw [hz]; abel
  have hp : C.realPt z = embR C.X y := by
    rw [← a1, hr, hadd, hfin _ a2, zero_add]
  have e1 : w + finW S T y = ratW T S yᵀ + (w - z) := by rw [hz]; abel
  have hzz : symplOH S T z z = 0 := by
    unfold symplOH
    rw [(_root_.GlobalTheory.FormMatch.forms_match D S T C).2.2.2.2.1, mul_zero]
  have e2 : -symplOH S T (ratW T S yᵀ) (w - z) = symplOH S T w z := by
    have e3 : symplOH S T z w = symplOH S T z (w - z) + symplOH S T z z := by
      rw [← symplOH_add_right, sub_add_cancel]
    rw [hr, symplOH_add_left, (symplOH_fin_real S T _ _ a2 (isRealPt_sub hw a3)).1, zero_add, symplOH_skew S T z w,
      e3, hzz, add_zero]
  unfold Ctx.rho heisO
  rw [(symplOH_fin_real S T _ _ a2 hw).2, AddChar.map_zero_eq_one, one_mul, e1, hf.quasi, e2, h2 w z hw a3, hp]

theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem isTh_actO (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T}
    (hγ' : γ' ∈ GQ T) : C.IsTh fun w => f (actO S T γ γ' w) := by
  have hs : ∀ w w', symplOH S T (actO S T γ γ' w) (actO S T γ γ' w') = symplOH S T w w' := fun w w' => by
    unfold symplOH
    rw [(_root_.GlobalTheory.FormMatch.forms_match D S T C).2.2.2.2.2.2.1]
  obtain ⟨R, -, -, -, -, -, -, -, -, hact⟩ := _root_.GlobalTheory.KerReal.real_points D S T C
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
    obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
    have e : actO S T γ γ' (ratW T S x) = ratW T S (m' * x * m) := by
      unfold actO ratW
      rw [hm, hm', Matrix.map_mul, Matrix.map_mul]
    rw [actO_add, ← hs, e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu ((hact γ γ' u).2.1 h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← hs w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have := hf.smooth k (A.comp L) (hA.comp h1) (fun t => (hact γ γ' (L t)).1 (h2 t)) (actO S T γ γ' w)
    simp only [actO_add]
    exact this

theorem theta_space_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), C.IsTh 0 ∧ (∀ f f', C.IsTh f → C.IsTh f' → C.IsTh (f + f') ∧ ((∀ w, IsRealPt w → f w = f' w) → f = f')) ∧ ∀ f, C.IsTh f → (∀ a : ℂ, C.IsTh (a • f)) ∧ (∀ w, C.IsTh (C.rho w f)) ∧ (∀ w w', C.rho w (C.rho w' f) = C.ψ (symplOH S T w w') • C.rho (w + w') f) ∧ (∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) w, IsRealPt w → C.rho (finW S T y) f w = cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y))) ∧ (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, C.IsTh fun w => f (actO S T γ γ' w)) ∧ ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  intro D S T C
  have hz : C.IsTh 0 := {
    quasi γ w := by simp only [Pi.zero_apply, mul_zero]
    level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
    cont := continuous_const
    smooth k L _ _ w := contDiff_const }
  have ha {f g : WO S T → ℂ} (hf : C.IsTh f) (hg : C.IsTh g) : C.IsTh (f + g) := {
    quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
    cont := hf.cont.add hg.cont
    smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w) }
  have hs (c : ℂ) {f : WO S T → ℂ} (hf : C.IsTh f) : C.IsTh (c • f) := {
    quasi γ w := by rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    cont := hf.cont.const_smul c
    smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w) }
  refine ⟨hz, fun f f' hf hf' => ⟨ha hf hf', fun h => ?_⟩, fun f hf =>
    ⟨fun a => hs a hf, isTh_rho C hf, fun w w' => heisO_heisO _ _ _ _ _ _, rho_finW C hf,
      fun γ hγ γ' hγ' => isTh_actO C hf hγ hγ', exists_level C hf⟩⟩
  exact sub_eq_zero.1 (eq_zero_of_real C (isTheta_sub hf hf') fun w hw => sub_eq_zero.2 (h w hw))

end GlobalTheory.ThetaSpace

end
end

