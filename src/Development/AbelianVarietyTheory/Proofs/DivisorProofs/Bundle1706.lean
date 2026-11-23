module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDegreeNonposOfAdelicDegreeNonpos
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem closedPoint_mem_nonzeroLocus {K : Type} [Field K] {C : Scheme.{0}} [IsIntegral C] (x : Sp K ⟶ C)
    [IsDominant x] {L : LB C} {σ : L.Sec} (hσ : σ ≠ 0) : x (IsLocalRing.closedPoint K) ∈ Out.nonzeroLocus σ := by
  have h : ∃ i, σ.f i ≠ 0 := by
    by_contra h
    push Not at h
    apply hσ
    obtain ⟨f, hf⟩ := σ
    obtain rfl : f = fun _ => 0 := funext h
    rfl
  obtain ⟨i, hi⟩ := h
  have hne : ((C.basicOpen (σ.f i) : C.Opens) : Set C).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e
    exact hi ((basicOpen_eq_bot_iff _).1 (Opens.ext e))
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open (C.basicOpen (σ.f i)).isOpen hne
  obtain rfl : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  exact Opens.mem_iSup.2 ⟨i, hy⟩

theorem deg_pos_of_integral {k K : Type} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] {r : ℕ}
    {g : Place k K → Matrix (Fin r) (Fin r) K} (hg : admitted g) {f : K} (hf : f ≠ 0)
    (hfin : {v : Place k K | v.1 f ≠ 1}.Finite) (hsum : ∑ᶠ v : Place k K, ord v f = 0) {m : ℕ}
    (hle : ∀ v : Place k K, v.1 (f * (g v).det ^ m) ≤ 1) {w : Place k K} (hlt : w.1 (f * (g w).det ^ m) < 1) :
    0 < deg g := by
  have hne : ∀ v, f * (g v).det ^ m ≠ 0 := fun v => mul_ne_zero hf (pow_ne_zero _ (hg.1 v))
  have hadd : ∀ v : Place k K, ord v (f * (g v).det ^ m) = ord v f + m * ord v (g v).det := fun v => by
    rw [(ord_calculus k K v).1 _ _ hf (pow_ne_zero _ (hg.1 v)), ← (ord_calculus k K v).2.1 _ (hg.1 v), zpow_natCast]
  have f₁ : (Function.support fun v : Place k K => ord v f).Finite :=
    hfin.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ hf).1 e)
  have f₂ : (Function.support fun v : Place k K => ord v (g v).det).Finite :=
    hg.2.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ (hg.1 v)).1 e.2)
  have f₃ : (Function.support fun v : Place k K => (m : ℤ) * ord v (g v).det).Finite :=
    f₂.subset fun v hv e => hv (by simp only [e, mul_zero])
  have hs : ∑ᶠ v : Place k K, ord v (f * (g v).det ^ m) = m * deg g := by
    simp only [hadd]
    rw [finsum_add_distrib f₁ f₃, hsum, zero_add, deg, mul_finsum' _ _ f₂]
  have h0 : ∀ v : Place k K, 0 ≤ ord v (f * (g v).det ^ m) := fun v =>
    ((ord_calculus k K v).2.2.1 _ (hne v)).1 (hle v)
  have hw : 0 < ord w (f * (g w).det ^ m) :=
    (h0 w).lt_of_ne fun e => hlt.ne (((ord_calculus k K w).2.2.2.1 _ (hne w)).2 e.symm)
  have f₄ : (Function.support fun v : Place k K => ord v (f * (g v).det ^ m)).Finite := by
    refine (f₁.union f₃).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    exact hv (by simp only [hadd, h.1, h.2, add_zero])
  have hpos : 0 < (m : ℤ) * deg g := by
    rw [← hs]
    exact hw.trans_le (single_le_finsum w f₄ h0)
  by_contra h
  exact absurd hpos (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg m) (not_lt.1 h)))

theorem interNum_det_nonpos_of_deg_nonpos : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → deg g ≤ 0 → interNum k (GlobalTheory.structureModule C) ![det W r] ≤ 0 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s g hV hs hg hloc hdeg
  by_contra hpos
  have := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2
  have := hx.2.1.1
  obtain ⟨m, σ, c, -, hσ, hc⟩ := _root_.GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos k C hx.1 (det W r) hW.isLB_det (not_le.1 hpos)
  obtain ⟨w, b, hb, hbc⟩ := _root_.GlobalTheory.Nef.centre_place k K C x hx c fun e => hc (e ▸ closedPoint_mem_nonzeroLocus x hσ)
  obtain ⟨f, hf, H⟩ := _root_.GlobalTheory.Nef.sec_detPow_rational k K C x hx W r hW V₀ s hV hs m σ hσ
  obtain ⟨hfin, hsum⟩ := _root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k K (_root_.GlobalTheory.Nef.CurveFF.isFF_of_isGenOver k K C x hx) f hf
  exact (deg_pos_of_integral hg hf hfin hsum (fun v => (H v _ (hloc v)).1)
    ((H w _ (hloc w)).2 b hb (hbc ▸ hc))).not_ge hdeg

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalStabilizer_doubledVacuum_eigenvalue_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegel.eigen_eq_one_of_diag | exact GlobalTheory.DblVacSiegel.eigen_eq_one_of_diag | (intros; apply GlobalTheory.DblVacSiegel.eigen_eq_one_of_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValueStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.distribHaarChar_supportedIdele_eq_localAbsValue : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (u : (AF F)ˣ), At (evFin F v) ((u : AF F) - 1) →
    ((MeasureTheory.distribHaarChar (AF F) u : NNReal) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := by
  first | exact @GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at | exact GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at | (intros; apply GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiag
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.PresImpl

variable {D : D7}

theorem schr_schr_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (x x₁ x₀ y₁ y₀ : κ → R) (f : (κ → R) → ℂ) :
    ψ (x ⬝ᵥ y₁ + ⅟2 * x₁ ⬝ᵥ y₁) * (ψ ((x + x₁) ⬝ᵥ y₀ + ⅟2 * x₀ ⬝ᵥ y₀) * f (x + x₁ + x₀)) =
      ψ (⅟2 * (x₁ ⬝ᵥ y₀ - x₀ ⬝ᵥ y₁)) * (ψ (x ⬝ᵥ (y₁ + y₀) + ⅟2 * (x₁ + x₀) ⬝ᵥ (y₁ + y₀)) * f (x + (x₁ + x₀))) := by
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  refine congrArg (· * f (x + (x₁ + x₀))) (congrArg ψ ?_)
  have h2 : (2 : R) * ⅟2 = 1 := mul_invOf_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (-(x₁ ⬝ᵥ y₀)) * h2

theorem actO_eq (S T : HSp D) {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) (g : GA D S) (h : GA D T)
    (hh : mt T h = a.1.1) (hg : mt S g = (b⁻¹).1.1ᵀ) (w : Formalism.IndefR.Datum.WO S T) :
    Formalism.IndefR.Datum.actO S T g h w = GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (a, b) w := by
  have h1 : mt S g⁻¹ * mt S g = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : mt S g * (b.1.1)ᵀ = 1 := by
    rw [hg, ← Matrix.transpose_mul, ← Units.val_mul]
    simp
  have h3 : mt S g⁻¹ = (b.1.1)ᵀ := by
    calc mt S g⁻¹ = mt S g⁻¹ * (mt S g * (b.1.1)ᵀ) := by rw [h2, Matrix.mul_one]
      _ = (b.1.1)ᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [Formalism.IndefR.Datum.actO, GlobalTheory.WeilM.actAB, hh, h3]

theorem thetaTr_rho (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {ξ : AF D.host.F ⊗[D.host.F] D.host.E}
    (hs : ∀ x y : Formalism.IndefR.Datum.WO S T,
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
        Formalism.IndefR.Datum.symplO S T x y) {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (w : Formalism.IndefR.Datum.WO S T) (φ : (κ → AF D.host.F) → ℂ) :
    thetaTr D.host.F co ψ (co.rho ψ w φ) = Formalism.IndefR.Datum.heisO ψ S T w (thetaTr D.host.F co ψ φ) := by
  funext v
  have hhalf : algebraMap D.host.F (AF D.host.F) (1 / 2) = ⅟(2 : AF D.host.F) := by
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  have hf := co.form v w
  simp only [thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, Formalism.IndefR.Datum.heisO, GlobalTheory.WeilM.schr,
    Formalism.IndefR.Datum.symplOH, ← hs, hf, hhalf, map_add, Prod.fst_add, Prod.snd_add]
  rw [← tsum_mul_left]
  exact tsum_congr fun x => schr_schr_apply ψ _ _ _ _ _ φ


set_option maxHeartbeats 400000 in
theorem pres_impl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om p φ ∈ GlobalTheory.WeilM.schA D.host.F κ) ∧
                       ∀ p w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                         om p (co.rho ψ w φ) = co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p w) (om p φ) := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hB κ _ co hco ω hω om htr
  have key : ∀ p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB), ∃ (g : GA D S) (h : GA D T),
      mt T h = p.1.1.1 ∧ mt S g = (p.2⁻¹).1.1ᵀ := fun p => _root_.GlobalTheory.WeilSchrodinger.match_pair D S T JA JB ξ hA hB p.1 p.2
  have pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om p φ ∈ GlobalTheory.WeilM.schA D.host.F κ := by
    intro p φ hφ
    obtain ⟨g, h, hh, hg⟩ := key p
    exact (htr p.1 p.2 g h hh hg φ hφ).1
  refine ⟨pres, fun p w φ hφ => ?_⟩
  obtain ⟨a, b⟩ := p
  obtain ⟨g, h, hh, hg⟩ := key (a, b)
  have hs := _root_.GlobalTheory.WeilSchrodinger.symp_eq_symplO D S T JA JB ξ hA hB
  have hrho : ∀ w', ∀ φ' ∈ GlobalTheory.WeilM.schA D.host.F κ, co.rho ψ w' φ' ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun w' φ' h' => _root_.GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ _ φ' h'
  have h1 := htr a b g h hh hg _ (hrho w φ hφ)
  have h2 := htr a b g h hh hg _ hφ
  have hF := _root_.GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
  have E1 := hω.om_heis g h w _ hF
  have E2 := thetaTr_rho ψ S T hs co w φ
  have E3 := thetaTr_rho ψ S T hs co (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (a, b) w) (om (a, b) φ)
  have E4 := actO_eq S T a b g h hh hg w
  have E : thetaTr D.host.F co ψ (om (a, b) (co.rho ψ w φ)) =
      thetaTr D.host.F co ψ (co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (a, b) w) (om (a, b) φ)) := by
    refine h1.2.trans ?_
    refine (congrArg (ω (g, h)) E2).trans ?_
    refine E1.trans ?_
    refine Eq.trans ?_ E3.symm
    exact congrArg₂ (Formalism.IndefR.Datum.heisO ψ S T) E4 h2.2.symm
  unfold thetaTr GlobalTheory.WeilM.Darboux.rho at E
  refine _root_.GlobalTheory.SchrodingerUniq.main D ψ hψ κ _ h1.1 _ (hrho _ _ h2.1) fun v => ?_
  obtain ⟨v', rfl⟩ := co.e.surjective v
  exact congrFun E v'

end GlobalTheory.WeilSchrodinger.PresImpl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenvalueEqOneInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacSiegelV
open GlobalTheory.DblVacSiegel

theorem eigen_eq_one_of_diag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv d' _ dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  change omd p (boxFun Ψ (fun x => star (Ψ x))) =
    μ • boxFun Ψ (fun x => star (Ψ x)) at hμ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin a) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.V) (s : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.DblVac.matD g * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin a → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t⁻¹ : GL (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) *
          ((t⁻¹ : GL (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hwT : w ∉ above E (X.T : Set (Pl (F := F))) := fun h => hv (by rw [← under_eq_of_isInertAt hw]; exact h)
  have hunr : UnrAt (X.β / X.α) w := by
    rw [div_eq_mul_inv]
    exact (hT.chars.unrβ w hwT).mul (hT.chars.unrα w hwT).inv
  have hβ : (X.β / X.α) (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine chr_det_eq_one G.V hT.geo.hV.lat hw hunr t (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (u • ((t : Matrix (Fin a) (Fin a) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  have he := congrArg (DiagForm.lDiag F (Fin a × Fin (a + a'))) hμ
  rw [map_smul, smul_eq_mul] at he
  have hrule := he.symm.trans hrule
  rw [hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl hrule
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

end GlobalTheory.DblVacSiegelV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumHeisenbergEigenDoubledLatticeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_heisenbergEigen_doubledLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) (boxFun (G.M.vac v) (fun x => star (G.M.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))))) := by
  first | exact @GlobalTheory.DblVacEigen.doubled_vac_eigen | exact GlobalTheory.DblVacEigen.doubled_vac_eigen | (intros; apply GlobalTheory.DblVacEigen.doubled_vac_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLatticStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_twistedVacuumCondition_doubledLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))))) := by
  first | exact @GlobalTheory.DblVacLine.dbl_vac_acts | exact GlobalTheory.DblVacLine.dbl_vac_acts | (intros; apply GlobalTheory.DblVacLine.dbl_vac_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationAutomorphismCommutesSchwartz
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.EvSymmTame

open Filter
open scoped Classical

theorem isTame_symm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e →
    Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) → IsTame F T.symm.toLinearMap := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM hM₁ e hE hbij T hT g hg
  have hA : ∀ Φ ∈ schA F (Fin n × Fin d), T.symm (e Φ) = Φ := fun Φ hΦ => by
    rw [← hT Φ hΦ, LinearEquiv.symm_apply_apply]
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hbi : Function.Bijective ei :=
    ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hM e hbij.injOn ei ev (fun v => (hev v).1) hloc,
      GlobalTheory.ArchSurj.surjective_arch F E σ B n d X W M M₁ hM hM₁ e hbij.surjOn ei ev hev hloc⟩
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse _ _ ei hbi
  have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
    intro j v
    by_cases h : φ j v = M₁.vac v
    · exact ⟨M.vac v, (hM.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
    · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
      obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
      exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
  choose ψ hψSB hψev hψvac using hpre
  have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
    ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
  have hψstd : ∀ j, ∀ᶠ v in cofinite,
      ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hψfam j).and hM.std).mono fun v hv => hv.1.trans hv.2
  have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
      SB (Fin n × Fin d → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  refine ⟨Fin m, inferInstance, fun j => c j • S, fun j y => ∏ᶠ v, ψ j v fun i => evalV F v (y i), hG, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl
  have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
      e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
    intro j
    have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
    rw [hS] at h1
    have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
    rw [h2] at h1
    exact h1.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearEquiv.coe_toLinearMap, hsplit, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hφe j, hA _ (Submodule.subset_span ⟨S f, _, hG j, rfl⟩)]
  funext x
  simp [pureA, mul_assoc]

end GlobalTheory.EvSymmTame
end
end

