module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrime

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussVacuumNondegenerateGaussianDualPair
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.GaussVacPair
open GlobalTheory.GaussFockJ GlobalTheory.ThK.EvAt0.PolD

theorem actsD_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ f₂ : SInf F κ}
    (h1 : ActsD (evI F) T f f₁) (h2 : ActsD (evI F) T f f₂) : f₁ = f₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) κ
  ext y
  have hr := hR f
  let x : κ → AF F := fun i => liftA (y i)
  have hx : At (evI F) x := fun c hc => funext fun i => smul_liftA hc (y i)
  have e := (h1 R hr x).unique (h2 R hr x)
  have hRx : R x = R 0 := by
    have := hr.1 0 x hx
    rwa [zero_add] at this
  have hl : (fun i => evI F (x i)) = y := funext fun i => evI_liftA (y i)
  simp only [tens, hl, hRx] at e
  exact mul_right_cancel₀ hR0 e

theorem exists_gauss_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧
      ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ) (c : ℝ),
        0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ ∀ x, g x = Complex.exp (-(Q x x)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨J₀, hJJ, hJω, hJpos, hJrel⟩ := GlobalTheory.T.exists_positive_complex_structure_darboux_pair F E σ B n d X W M χX χW om r s r' s' hP
  have hsym : ∀ x y : (Fin n × Fin d → mixedEmbedding.mixedSpace F), GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x y = GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) y x := by
    intro x y
    simp only [GlobalTheory.GaussLine.pairInf_apply, mul_comm]
  obtain ⟨Q, c, hc, hQc, hQs, hQJ⟩ := _root_.GlobalTheory.siegel_fock_exists (Fin n × Fin d → mixedEmbedding.mixedSpace F) (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) J₀ hsym hJJ hJω hJpos
  obtain ⟨g, hg, hgd⟩ := _root_.GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form (Fin n × Fin d → mixedEmbedding.mixedSpace F) Q c hc hQc
  refine ⟨g, ⟨fun _ => 1, ?_⟩, Q, c, hc, hQc, hg⟩
  intro u u' hu hu' hrel f f' hf hf'
  have hrel' : ∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    rw [hrel w]
    simp
  have key : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) v → ∀ h : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ v) g h → ∀ x, h x = GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (Psi M v) g x := by
    intro v hv h hh x
    have h0 := actsD_Phi hψ M (Psi M v) g
    rw [Phi_Psi M hv] at h0
    rw [actsD_unique hh h0, dHeis_eq_dOp]
  have hJ : Psi M u' = J₀ (Psi M u) := hJrel u u' hu hu' hrel'
  have hd : ∀ (w : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) w g x =
      -2 * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x w.2 : ℂ)) * g x := by
    intro w x
    rw [GlobalTheory.GaussLine.dHeis, hgd x w.1, hQs w.1 x]
    ring
  ext x
  rw [SchwartzMap.smul_apply, key u' hu' f' hf' x, key u hu f hf x, hJ, hd, hd, hQJ, smul_eq_mul]
  ring

end GlobalTheory.GaussVacPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianEvalRingPointNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

namespace GlobalTheory


open GlobalTheory.TopForm in
theorem CanonLB.exists_jacobian_evalPt_ne_zero : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type} [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i), ∃ g : Fin D → Γ(Y, K.bundle.U i), evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0 := by
  intro k _ Y p D _ K i F _ z hz
  by_contra hcon
  push_neg at hcon
  let Sm : Submodule Γ(Y, K.bundle.U i) (FormsOn p D (K.bundle.U i)) :=
    Submodule.comap (K.coeff i le_rfl) (RingHom.ker (evalPt z _ hz))
  have hsub : Set.range (dForm (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (K.bundle.U i)) (D := D)) ⊆ (Sm : Set _) := by
    rintro _ ⟨g, rfl⟩
    exact (RingHom.mem_ker).2 (hcon g)
  have hle : (⊤ : Submodule Γ(Y, K.bundle.U i) (FormsOn p D (K.bundle.U i))) ≤ Sm := by
    rw [← span_dForm (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (K.bundle.U i)) D]
    exact Submodule.span_le.2 hsub
  have hmem : resForm (le_rfl : K.bundle.U i ≤ K.bundle.U i) (K.om i) ∈ Sm := hle Submodule.mem_top
  have h1 : evalPt z _ hz (K.coeff i le_rfl (resForm le_rfl (K.om i))) = 0 :=
    (RingHom.mem_ker).1 hmem
  rw [K.coeff_om, map_one] at h1
  exact one_ne_zero h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieTieOfFrMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.TieFrame

theorem one_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  have e := h.2 T 1 1 (pushPt h.1.w 1) (pushPt h.1.w 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : pushPt h.1.w (1 : T ⟶ G') = 1 := mul_eq_left.1 (Over.OverMorphism.ext e)
  refine (congrArg Over.Hom.left e').trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  exact Category.assoc _ _ _

theorem exists_hom {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {A : Over (Sp K)} [GrpObj A]
    {φ : A.left ⟶ G.left} {φ' : A.left ⟶ G'.left} (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback A G (spMap (algebraMap V K)) φ) (hφ' : IsGrpPullback A G' (spMap (algebraMap V K)) φ') :
    ∃ F : G ⟶ G', IsMonHom F ∧ φ ≫ F.left = φ' := by
  obtain ⟨e, he, h₁⟩ := grpPullback_iso hφ (isGrpPullback_pullback G _)
  obtain ⟨e', he', h₂⟩ := grpPullback_iso hφ' (isGrpPullback_pullback G' _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := HomExtExamples.homExtSt_holds V K G G' hG hG' (e.inv ≫ e'.hom) inferInstance
  have a : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G'.hom _ =
      pullback.fst G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  refine ⟨F, hF, ?_⟩
  rw [← h₁, Category.assoc, ← a, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, h₂]

theorem dual_w {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  rw [spMap_spMap, spMap_spMap]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_pull {V O : Type} [CommRing V] [CommRing O] {G : Over (Sp V)} [GrpObj G] {G' : Over (Sp O)} [GrpObj G']
    {f : V →+* O} {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) π) {u : epsOver V V ⟶ G} (hu : IsTan u) :
    ∃ x : LieG G', x.1.left ≫ π = spMap (dualMap f) ≫ u.left := by
  have w : (spMap (dualMap f) ≫ u.left) ≫ G.hom = spMap (algebraMap O (DualNumber O)) ≫ spMap f := by
    rw [Category.assoc, Over.w u, ← dual_w]
    rfl
  refine ⟨⟨Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ w), ?_⟩, h.1.lift_fst _ _ w⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  refine Eq.trans ?_ (one_comp h (specO O O)).symm
  change (spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ h.1.lift _ _ w) ≫ π = spMap (algebraMap O O) ≫ _
  have e : spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ spMap (dualMap f) =
      spMap f ≫ spMap (TrivSqZeroExt.fstHom V V V).toRingHom := by
    rw [spMap_spMap, spMap_spMap]
    congr 1
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [Category.assoc, h.1.lift_fst, ← Category.assoc, e, Category.assoc, hu, Hom.one_def, Over.comp_left,
    Over.toUnit_left]
  change spMap f ≫ spMap (algebraMap V V) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]

theorem exists_lieTie_of_frMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∃ x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt, ∀ τ j, LieTie P ψ (x τ j) (z.u τ j) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz
  letI := io.toAlgebra
  obtain ⟨hk, G, t', m₁, m₂, π, φ, hπ, -, hφ, h4, rfl, -⟩ := hP
  obtain ⟨G₀, t₀, n₁, n₂, ⟨ub, ht, -, -, hub⟩, -⟩ := y₀.2.2
  obtain ⟨e, he, h₁⟩ := grpPullback_iso n₁.cart m₁.cart
  have h₂ : IsGrpPullback t₀.G G.G (spMap (algebraMap T.V T.Fr)) (e.hom.left ≫ m₂.φ) :=
    ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl
  obtain ⟨F, hF, h₃⟩ := exists_hom G₀.semi G.semi n₂.cart h₂
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  suffices h : ∀ τ j, ∃ x : LieG P.Gt, LieTie P (φ ≫ m₁.φ) x (z.u τ j) by
    choose x hx using h
    exact ⟨x, hx⟩
  intro τ j
  obtain ⟨u', h5, h6⟩ := hub τ j
  have ht' : IsTan (ub τ j ≫ F) := by
    unfold IsTan
    rw [Over.comp_left, ← Category.assoc, ht τ j, ← Over.comp_left, MonObj.one_comp]
  obtain ⟨xG, hx⟩ := exists_pull hπ ht'
  have mem_pow {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  have dual_dvd (n : ℕ) (x : DualNumber O) :
      (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
    have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
      rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
    rw [e]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩
  have hadic : IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := by
    have h : IsAdicComplete (Ideal.span {(p : O)}) O := inferInstance
    refine { haus' := ?_, toIsPrecomplete := ?_ }
    · intro x hx
      simp only [SModEq.zero, mem_pow, dual_dvd] at hx
      refine TrivSqZeroExt.ext (h.toIsHausdorff.haus' x.fst fun n => ?_)
        (h.toIsHausdorff.haus' x.snd fun n => ?_)
      · rw [SModEq.zero, mem_pow]; exact (hx n).1
      · rw [SModEq.zero, mem_pow]; exact (hx n).2
    · constructor
      intro f hf
      simp only [SModEq.sub_mem, mem_pow, dual_dvd] at hf ⊢
      obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec' (fun n => (f n).fst) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).1
      obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec' (fun n => (f n).snd) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).2
      simp only [SModEq.sub_mem, mem_pow] at ha hb
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩
  obtain ⟨x, hc, -⟩ := existsUnique_left (P := P) hp hadic xG.1
  have h7 := hc.comp (TrivSqZeroExt.fstHom O O O)
  rw [xG.2] at h7
  have hu : (u' ≫ e.hom.left) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    haveI : Mono (spMap (algebraMap T.V T.Fr)) :=
      haveI : IsPreimmersion (spMap (algebraMap T.V T.Fr)) := IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
      inferInstance
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, Category.assoc, ← m₂.cart.1.w,
      ← Category.assoc e.hom.left, ← h₃, Category.assoc, Over.w F, ← Category.assoc, h6, Category.assoc,
      Over.w (ub τ j), ← dual_w]
    rfl
  have w : (spMap (dualMap k.toRingHom) ≫ u' ≫ e.hom.left) ≫ t'.G.hom =
      spMap (algebraMap C (DualNumber C)) ≫ spMap k.toRingHom := by
    rw [Category.assoc, hu, dual_w]
  refine ⟨⟨x, (existsUnique_left (P := P) hp₀ inferInstance 1).unique h7 Corr.one⟩, xG,
    Over.homMk (hφ.1.lift _ _ w) (hφ.1.lift_snd _ _ w), hc, ?_, hπ.1.hom_ext ?_ ?_⟩
  · change hφ.1.lift _ _ w ≫ _ = _
    rw [hφ.1.lift_fst_assoc, hz.2.1, ← h5, Category.assoc, Category.assoc, h₁]
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, ← h4, hφ.1.lift_fst_assoc, Category.assoc, Category.assoc, ← h₃, ← Category.assoc u', h6,
      Category.assoc, Category.assoc, hx, ← Category.assoc, ← Category.assoc (spMap _) (spMap _), spMap_spMap,
      spMap_spMap, Over.comp_left]
    congr 2
    refine RingHom.ext fun s => TrivSqZeroExt.ext ?_ ?_
    · simpa [dualMap] using (hk s.fst).symm
    · simpa [dualMap, Algebra.algebraMap_eq_smul_one] using (hk s.snd).symm
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, P.gen_pull.1.w, hφ.1.lift_snd_assoc, Category.assoc, Over.w xG.1]
    exact (dual_w _).symm

end GlobalTheory.CompHt.TieFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.RecSpan

open GlobalTheory.HTLat.OmegaRank

theorem exists_eigenbasis {V O : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing O]
    [Algebra V O] [Module.Flat V O] (G : Over (Sp V)) [GrpObj G] [Smooth G.hom] {Λ : Type} (act : Λ → (G ⟶ G))
    [∀ a, IsMonHom (act a)] (χ : Λ → V) {m : ℕ} (u : Fin m → (epsOver V V ⟶ G)) (ht : ∀ i, IsTan (u i))
    (he : ∀ i a, (u i ≫ act a).left = spMap (epsMul (χ a)) ≫ (u i).left)
    (hb : ∀ w : epsOver V V ⟶ G, IsTan w → (∀ a, (w ≫ act a).left = spMap (epsMul (χ a)) ≫ w.left) →
      ∃! c : Fin m → V, IsComb u c w)
    {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (spMap (algebraMap V O)) π)
    (act' : Λ → (G' ⟶ G')) (ha : ∀ a, (act' a).left ≫ π = π ≫ (act a).left) :
    ∃ u' : Fin m → (specO O (DualNumber O) ⟶ G'),
      (∀ i, (u' i).left ≫ π = spMap (dualMap (algebraMap V O)) ≫ (u i).left) ∧
      ∀ w : LieG G', (∀ a, w.1 ≫ act' a = ptMap (dualScale (algebraMap V O (χ a))) ≫ w.1) →
        ∃ c : Fin m → O, w.1 = (List.ofFn fun i => ptMap (dualScale (c i)) ≫ u' i).prod := by
  obtain ⟨u', -, -, h3, h4⟩ := PlaceInt.Ext.exists_eigenbasis_pullback (V' := O) G act χ u ht he hb
  obtain ⟨e, he, he'⟩ := grpPullback_iso hπ (isGrpPullback_pullback G _)
  refine ⟨fun i => u' i ≫ e.inv, fun i => ?_, fun w hw => ?_⟩
  · rw [← he', ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact h4 i
  · have hc : ∀ a, e.hom ≫ (Over.pullback (spMap (algebraMap V O))).map (act a) = act' a ≫ e.hom := fun a => by
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      have A : ((Over.pullback (spMap (algebraMap V O))).map (act a)).left ≫ pullback.fst G.hom _ =
        pullback.fst G.hom _ ≫ (act a).left := pullback.lift_fst _ _ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, A, he', ha, ← Category.assoc, he']
    obtain ⟨c, ⟨y, hy, hy'⟩, -⟩ := h3 (w.1 ≫ e.hom) (by
      have h := congrArg (fun z => (z ≫ e.hom).left) w.2
      simp only [Category.assoc, IsMonHom.one_hom] at h
      exact h) fun a => by
        have h := congrArg (fun z => (z ≫ e.hom).left) (hw a)
        simp only [Category.assoc, ← hc] at h
        exact h
    refine ⟨c, ?_⟩
    have h := congrArg (IsMonHom.monoidHom e.inv _) hy'
    rw [map_list_prod, List.map_ofFn] at h
    refine Eq.trans ?_ (h.trans ?_)
    · exact ((Category.assoc _ _ _).trans (by rw [e.hom_inv_id, Category.comp_id])).symm
    · congr 2
      funext i
      exact (congrArg (· ≫ e.inv) (show y i = ptMap (dualScale (c i)) ≫ u' i from Over.OverMorphism.ext (hy i))).trans
        (Category.assoc _ _ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [StarRing (𝓞 E)] {P : Point p v O (𝓞 E)}

theorem exists_map_to_model {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
    [IsFractionRing V F] {x₀ : Sp F ⟶ Xo.X} {k : F →+* C} {kO : V →+* O} {ψ : P.A.A.left ⟶ Xo.univ.t.G.left}
    (h : PointOver P x₀ k kO ψ) {G : SAB H (Sp V)} {t : SAB H (Sp F)} (n₁ : SABMap t Xo.univ.t x₀)
    (n₂ : SABMap t G (spMap (algebraMap V F))) :
    ∃ (π : P.G.left ⟶ G.G.left) (φ : P.A.A.left ⟶ t.G.left), IsGrpPullback P.G G.G (spMap kO) π ∧
      (∀ a, (P.oG.act a).left ≫ π = π ≫ (G.act.act a).left) ∧ φ ≫ t.G.hom = P.A.A.hom ≫ spMap k ∧
      φ ≫ n₂.φ = P.gen ≫ π ∧ φ ≫ n₁.φ = ψ := by
  obtain ⟨-, G', t', m₁, m₂, π, φ, h1, h2, h3, h4, rfl, -⟩ := h
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso m₁.cart n₁.cart
  obtain ⟨e, he, he'⟩ := LocModelLie.exists_iso_of_models HomExtExamples.homExtSt_holds V F G'.G G.G G'.semi G.semi t'.G
    m₂.cart (((isGrpPullback_of_iso a).comp n₂.cart).congr (Category.id_comp _) rfl)
  have c₁ : ∀ b, (t'.act.act b).left ≫ a.hom.left = a.hom.left ≫ (t.act.act b).left := fun b =>
    n₁.cart.1.hom_ext (by rw [Category.assoc, Category.assoc, n₁.act, ha', m₁.act, ← Category.assoc, ha'])
      (by rw [Category.assoc, Category.assoc, Over.w, Over.w, Over.w, Over.w])
  have c₂ : ∀ b, (G'.act.act b).left ≫ e.hom.left = e.hom.left ≫ (G.act.act b).left := fun b => by
    haveI := G.semi.separated
    haveI := G'.semi.smooth
    haveI : IsSchemeTheoreticallyDominant (spMap (algebraMap V F)) :=
      schDom_spec_map _ (IsFractionRing.injective V F)
    haveI : IsSchemeTheoreticallyDominant m₂.φ := .of_isPullback m₂.cart.1.flip
    refine ext_of_schDom G.G.hom (by rw [Category.assoc, Category.assoc, Over.w, Over.w, Over.w, Over.w]) m₂.φ ?_
    rw [← Category.assoc, ← m₂.act, Category.assoc, he', ← Category.assoc, c₁, ← Category.assoc m₂.φ, he',
      Category.assoc, Category.assoc, n₂.act]
  refine ⟨π ≫ e.hom.left, φ ≫ a.hom.left, (h1.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl,
    fun b => ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, h2, Category.assoc, Category.assoc, c₂]
  · rw [Category.assoc, Over.w, h3.1.w]
  · rw [Category.assoc, ← he', ← Category.assoc, h4, Category.assoc]
  · rw [Category.assoc, ha']

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    (dualMap f).comp (dualMap g) = dualMap (f.comp g) := by
  ext s <;> simp [dualMap]

theorem dualMap_alg {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  rw [spMap_spMap, spMap_spMap]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem ext_generic {y y' : specO O (DualNumber O) ⟶ P.G}
    (h : spMap (dualMap (algebraMap O C)) ≫ y.left = spMap (dualMap (algebraMap O C)) ≫ y'.left) : y = y' := by
  haveI : IsSchemeTheoreticallyDominant (spMap (dualMap (algebraMap O C))) :=
    (schemeDominant_specMap_iff _).2 fun a b hab => TrivSqZeroExt.ext
      (P.integers.hom_inj (by simpa [dualMap] using congrArg TrivSqZeroExt.fst hab))
      (P.integers.hom_inj (by simpa [dualMap, Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd hab))
  haveI := P.semi.separated
  exact Over.OverMorphism.ext (ext_of_schDom P.G.hom ((Over.w y).trans (Over.w y').symm) _ h)

theorem span_bLie_eq_wRec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∀ (τ : E →+* ℂ) (x : Fin (Dw.mult τ) → LieG P.Gt), (∀ j, LieTie P ψ (x j) (z.u τ j)) → Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec (embInt c P.integers τ) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz τ x hx
  letI := io.toAlgebra
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact ⟨⟨x j, (hx j).isEig hP (z.eig τ j)⟩, rfl⟩
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨G, t, n₁, n₂, ⟨ub, u₁, u₂, u₃, u₄⟩, -⟩ := y₀.2.2
  obtain ⟨π, φ, h1, h2, h3, h4, h5⟩ := exists_map_to_model hP n₁ n₂
  letI := kO.toAlgebra
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  have inj : Function.Injective (algebraMap T.V O) := fun a b h => IsFractionRing.injective T.V T.Fr
    (k.toRingHom.injective ((hP.1 a).symm.trans ((congrArg _ h).trans (hP.1 b))))
  haveI : FaithfulSMul T.V O := (faithfulSMul_iff_algebraMap_injective _ _).2 inj
  haveI : Module.Flat T.V O := inferInstance
  haveI := G.semi.smooth
  haveI := G.act.hom
  choose χ hχ using fun a => int_val c T io τ a
  have hχ' : ∀ a, algebraMap T.V O (χ a) = embInt c P.integers τ a := fun a => P.integers.hom_inj (by
    rw [algebraMap_embInt, ← k.commutes]
    exact (hP.1 _).trans (congrArg k (hχ a)))
  obtain ⟨u', v₁, v₂⟩ := exists_eigenbasis G.G G.act.act χ (ub τ) (u₁ τ) (fun i a => u₂ τ i a _ (hχ a))
    (fun w hw he => u₃ τ w hw fun a z hz => by
      obtain rfl : z = χ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ a).symm)
      exact he a) h1 P.oG.act h2
  have hc : ∀ j, Corr P (x j).1 (u' j) := fun j => by
    obtain ⟨xG, s, s₁, s₂, s₃⟩ := hx j
    obtain ⟨r, r₁, r₂⟩ := u₄ τ j
    have r₃ : r ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
      have : Mono (spMap (algebraMap T.V T.Fr)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
      refine (cancel_mono (spMap (algebraMap T.V T.Fr))).1 ?_
      have k : (ub τ j).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ j)
      rw [Category.assoc, ← n₂.cart.1.w, ← Category.assoc, r₂]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k).trans (dualMap_alg _))
    have e₁ : s.left ≫ φ = spMap (dualMap k.toRingHom) ≫ r := n₁.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, r₁, h5, s₂, hz.2.1])
      (by rw [Category.assoc, Category.assoc, r₃, h3, dualMap_alg, ← Category.assoc, Over.w s]; rfl)
    have e₂ : xG.1 = u' j := ext_generic (h1.1.hom_ext ?_ (by
      rw [Category.assoc, Category.assoc, Over.w, Over.w]))
    · exact e₂ ▸ s₁
    have e₃ : k.toRingHom.comp (algebraMap T.V T.Fr) = (algebraMap O C).comp (algebraMap T.V O) :=
      RingHom.ext fun a => (hP.1 a).symm
    rw [← s₃, Category.assoc, ← h4, ← Category.assoc, e₁, Category.assoc, r₂, Category.assoc, v₁, ← Category.assoc,
      ← Category.assoc, spMap_spMap, spMap_spMap, dualMap_comp, dualMap_comp, e₃]
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have mem_pow : ∀ {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R),
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
    intro R _ a n x
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  have dual_dvd : ∀ (n : ℕ) (x : DualNumber O),
      (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
    intro n x
    have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
      rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
    rw [e]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩
  have hadic : IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := by
    have h : IsAdicComplete (Ideal.span {(p : O)}) O := inferInstance
    refine { haus' := ?_, toIsPrecomplete := ?_ }
    · intro x hx
      simp only [SModEq.zero, mem_pow, dual_dvd] at hx
      refine TrivSqZeroExt.ext (h.toIsHausdorff.haus' x.fst fun n => ?_)
        (h.toIsHausdorff.haus' x.snd fun n => ?_)
      · rw [SModEq.zero, mem_pow]; exact (hx n).1
      · rw [SModEq.zero, mem_pow]; exact (hx n).2
    · constructor
      intro f hf
      simp only [SModEq.sub_mem, mem_pow, dual_dvd] at hf ⊢
      obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec' (fun n => (f n).fst) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).1
      obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec' (fun n => (f n).snd) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).2
      simp only [SModEq.sub_mem, mem_pow] at ha hb
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩
  have hl := existsUnique_left (P := P) hp hadic
  have hr := existsUnique_right (P := P) hp hadic
  obtain ⟨y, hy, -⟩ := hr w.1
  have y₁ := hy.comp (TrivSqZeroExt.fstHom O O O)
  rw [w.2] at y₁
  obtain ⟨a, ha⟩ := v₂ ⟨y, (existsUnique_right (P := P) hp₀ inferInstance 1).unique y₁ Corr.one⟩ fun a =>
    (hr _).unique (corr_act hy a) (by
      rw [hχ', show w.1 ≫ P.oGt.act a = _ from congrArg Subtype.val (hw a)]
      exact hy.comp _)
  let S : Submonoid (specO O (DualNumber O) ⟶ P.G) :=
    { carrier := {y | ∃ w : LieG P.Gt, Corr P w.1 y ∧ P.bLie w ∈ Submodule.span O (Set.range fun j => P.bLie (x j))}
      mul_mem' := by
        rintro _ _ ⟨a, a₁, a₂⟩ ⟨b, b₁, b₂⟩
        exact ⟨lieAdd a b, a₁.mul b₁, P.bLie_add a b ▸ Submodule.add_mem _ a₂ b₂⟩
      one_mem' := ⟨lieZero P.Gt, Corr.one, P.bLie_zero ▸ Submodule.zero_mem _⟩ }
  obtain ⟨w', w₁, w₂⟩ : y ∈ S := by
    rw [show y = _ from ha]
    refine S.list_prod_mem fun s hs => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hs
    exact ⟨AvDefs.lieScale P.Gt (a j) (x j), (hc j).comp _,
      P.bLie_scale (a j) (x j) ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)⟩
  obtain rfl : w = w' := Subtype.ext ((hl y).unique hy w₁)
  exact w₂

end GlobalTheory.CompHt.RecSpan
end
end

