module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceSeesawWScalarFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceUnitaryAdelicHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceSeesawWScalarFrameStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_conjTranspose_mul_eq_smul_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ (δ : w.adicCompletion E) (Bm : GL (Fin (a + a')) (w.adicCompletion E)), Valued.v δ = 1 ∧ σL δ = -δ ∧
      IsFrameAt w G.W.L Bm ∧
      (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E))ᵀ * G.W.J.map (algebraMap E (w.adicCompletion E)) *
        (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)).map σL = δ • 1 := by
  first | exact @GlobalTheory.SkewFrameInert.exists_inertPlace_seesawW_scalar_frame | exact GlobalTheory.SkewFrameInert.exists_inertPlace_seesawW_scalar_frame | (intros; apply GlobalTheory.SkewFrameInert.exists_inertPlace_seesawW_scalar_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceUnitaryAdelicHomStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_unitary_adelicHom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {n : ℕ} (X : Spc F E n) (P : GL (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) *
        (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = δ • 1 →
      ∀ {Γ : Type} [Group Γ] (φ : Γ →* GL (Fin n) (w.adicCompletion E)),
        (∀ g, (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = 1) →
        ∃ ι : Γ →* UA σ X.J, (∀ g, ι g ∈ UAt σ X (evFin F v)) ∧
          (∀ g, (mat (ι g)).map (locW h) = ((P * φ g * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
          (IsFrameAt w X.L P → ∀ g, φ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (w.adicCompletion E)) → ι g ∈ GlobalTheory.InertSph.KAt σ X v) := by
  first | exact @GlobalTheory.InertPlace.exists_hom_inert | exact GlobalTheory.InertPlace.exists_hom_inert | (intros; apply GlobalTheory.InertPlace.exists_hom_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelOppositeLagrangianUnitaryOp
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

theorem GlobalTheory.InertBridgeLine.locVac_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ s m : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
      GlobalTheory.Hk3.LocVac ρ m → ∃ c : ℂ, m = c • s := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hvT L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s m hs hm
  obtain ⟨unr, odd, intS, intT, hermS, hermT, hδ, psiInt, psiNe, hAt, hSurj, hLat, hPsi, hEq, hιS, hιT, hKS, hKT⟩ := hC
  obtain ⟨-, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  have h2 : evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
    have h2e : evFin F v (⅟(2 : AF F)) = algebraMap F (Fv F v) (2 : F)⁻¹ := by
      show evFin F v (algebraMap F (AF F) 2⁻¹) = _
      exact AlgHom.commutes _ _
    rw [h2e]
    exact GlobalTheory.LatVac.half_mem_adicCompletionIntegers F v (hTr.base.inert v w hin).1
  have hone : ∀ γ ∈ latAtV G.V' G.W v, B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E))
      ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) = 1 := fun γ hγ =>
    GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW v θ _ h2 γ hγ γ hγ
  have hm' : ∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
      (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) •
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) := by
    intro γ hγ
    rw [hone γ hγ, one_smul]
    obtain ⟨x, rfl⟩ := hSurj γ ((GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1 γ hγ)
    have hx := (hLat x).2 hγ
    have h := hρ x m
    rwa [hm x hx] at h
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul F E σ B a a' G X om om' hTr v w hin θ hθ hvac m m.2 hm'
  refine ⟨c, Subtype.ext ?_⟩
  rw [Submodule.coe_smul, hs]
  exact hc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnipotentAdditive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinBarCoords

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_algebraMap (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (u : AF F) :
    compFin F E v (algebraMap (AF F) (AE F E) u) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (evFin F v u) := rfl

theorem at_tensAt (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := by
  intro u hu
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right, compFin_algebraMap, hu, map_zero, mul_zero, map_zero]

theorem eq_tensAt_of_at (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {z : AE F E} (hz : At (evFin F v) z) :
    z = tensAt E v (compFin F E v z) := by
  have h1 : (1 - atPlace v 1) • z = 0 := hz _ (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [Algebra.smul_def, show algebraMap (AF F) (AE F E) (atPlace v 1) = tensAt E v 1 from rfl, tensAt_mul_right, one_mul]

theorem piW_tensAt (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) : piW t (tensAt E v y) = splitProj t y := by
  show splitProj t (compFin F E v (tensAt E v y)) = _
  rw [compFin_tensAt]

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_matrix {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {x : Matrix m n (AE F E)} :
    At (evFin F v) x ↔ ∀ i j, At (evFin F v) (x i j) := by
  constructor
  · intro h i j u hu
    have := congrFun (congrFun (h u hu) i) j
    simpa using this
  · intro h u hu
    ext i j
    simpa using h i j u hu

def liftM (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) :
    Matrix m n (Fv F v) × Matrix m n (Fv F v) →+ Matrix m n (AE F E) :=
  AddMonoidHom.mk' (fun p => Matrix.of fun i j => tensAt E v ((splitAlgEquiv hcm t).symm (p.1 i j, p.2 i j)))
    (fun p q => by ext i j; simp only [Prod.fst_add, Prod.snd_add, Matrix.add_apply, Matrix.of_apply, ← Prod.mk_add_mk, map_add (f := _)])

theorem liftM_at (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (p : Matrix m n (Fv F v) × Matrix m n (Fv F v)) : At (evFin F v) (liftM σ hcm v t p) :=
  (at_matrix v).2 fun _ _ => at_tensAt v _

theorem liftM_fst (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (p : Matrix m n (Fv F v) × Matrix m n (Fv F v)) : (liftM σ hcm v t p).map (piW t) = p.1 := by
  ext i j
  simp [liftM, piW_tensAt]

theorem liftM_snd (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (p : Matrix m n (Fv F v) × Matrix m n (Fv F v)) : (liftM σ hcm v t p).map (piW (t.comp σ)) = p.2 := by
  ext i j
  simp [liftM, piW_tensAt]

theorem eq_zero_of_at (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {m n : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v)
    {x : Matrix m n (AE F E)} (hx : At (evFin F v) x) (h1 : x.map (piW t) = 0) (h2 : x.map (piW (t.comp σ)) = 0) :
    x = 0 := by
  ext i j
  rw [eq_tensAt_of_at v ((at_matrix v).1 hx i j)]
  have e : compFin F E v (x i j) = 0 := split_ext hcm t (by rw [map_zero]; exact (by simpa using congrFun (congrFun h1 i) j : piW t (x i j) = 0))
    (by rw [map_zero]; exact (by simpa using congrFun (congrFun h2 i) j : piW (t.comp σ) (x i j) = 0))
  rw [e, map_zero]; rfl

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  set A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm with hA'
  have key : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA, hA', Matrix.transpose_submatrix,
      Matrix.submatrix_mul (Aᵀ * M) (A.map star) e.symm id e.symm Function.bijective_id,
      Matrix.submatrix_mul Aᵀ M e.symm id id Function.bijective_id, Matrix.submatrix_id_id, Matrix.submatrix_map]
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg,
    Matrix.det_one, mul_one, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0, mul_zero, zero_mul] at hd
  exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd.symm

theorem det_map_isUnit : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (r s : ℕ), c ≠ 0 → (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map (B.emb w).1) r s) →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v), IsUnit (J.map t).det := by
  intro F E _ _ _ _ _ B n J c r s hc hs v t
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h1 := det_ne_zero_of_hasSig (hs (NumberField.InfinitePlace.mk φ))
  have e1 : (J.map (B.emb (NumberField.InfinitePlace.mk φ)).1).det = (B.emb (NumberField.InfinitePlace.mk φ)).1 J.det :=
    (RingHom.map_det _ J).symm
  rw [Matrix.det_smul, e1] at h1
  have hJ : J.det ≠ 0 := fun h0 => h1 (by rw [h0, map_zero, mul_zero])
  have e2 : (J.map t).det = t J.det := (RingHom.map_det (t : E →+* Fv F v) J).symm
  rw [isUnit_iff_ne_zero, e2]
  exact (map_ne_zero_iff _ (t : E →+* Fv F v).injective).2 hJ

end GlobalTheory.LinBarCoords

namespace GlobalTheory.LinBarCoords
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.EmbChart

theorem exists_split_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (AE F E),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW t) = 0 ∧ GlobalTheory.LinBarAt.coAt G t (uT Y) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW (t.comp σ)) = 0 ∧ (uM z).map (piW t) = -z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinBarAt.coAt G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinBarAt.coAt G t x i j * (u.map (piW t)) i j) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v t
  have hcm := hTr.base.cm
  have hP : IsUnit (G.V'.J.map t).det := det_map_isUnit B G.V'.J 1 _ _ one_ne_zero (fun w => by rw [one_smul]; exact hTr.geo.hV'.sig w) v t
  have hQ : IsUnit ((G.W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose]; exact det_map_isUnit B G.W.J Complex.I _ _ Complex.I_ne_zero hTr.geo.hW.sig v t
  set P := G.V'.J.map t with hPdef
  set Q := (G.W.J.map t)ᵀ with hQdef
  let L := liftM σ hcm (m := Fin a') (n := Fin (a + a')) v t
  let uT : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun Y => L (0, -(P⁻¹ * Y * Q⁻¹))) (fun Y Y' => by
      rw [Matrix.mul_add, Matrix.add_mul, neg_add, ← map_add (f := _), Prod.mk_add_mk, add_zero])
  let uM : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun z => L (-z, 0)) (fun z z' => by rw [neg_add, ← map_add (f := _), Prod.mk_add_mk, add_zero])
  have hco : ∀ u, GlobalTheory.LinBarAt.coAt G t u = -(P * u.map (piW (t.comp σ)) * Q) := fun u => by
    simp [GlobalTheory.LinBarAt.coAt, hPdef, hQdef]
  have hTc : ∀ Y, (uT Y).map (piW (t.comp σ)) = -(P⁻¹ * Y * Q⁻¹) := fun Y => liftM_snd σ hcm v t _
  have hTt : ∀ Y, (uT Y).map (piW t) = 0 := fun Y => liftM_fst σ hcm v t _
  have hMc : ∀ z, (uM z).map (piW (t.comp σ)) = 0 := fun z => liftM_snd σ hcm v t _
  have hMt : ∀ z, (uM z).map (piW t) = -z := fun z => liftM_fst σ hcm v t _
  have hTa : ∀ Y, At (evFin F v) (uT Y) := fun Y => liftM_at σ hcm v t _
  have hMa : ∀ z, At (evFin F v) (uM z) := fun z => liftM_at σ hcm v t _
  refine ⟨uT, uM, fun Y => ⟨hTa Y, hTt Y, ?_⟩, fun z => ⟨hMa z, hMc z, hMt z⟩, fun u hu => ?_, fun x u hx hu => ?_⟩
  · have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
    have e2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
    rw [hco, hTc, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
  · refine ⟨GlobalTheory.LinBarAt.coAt G t u, -(u.map (piW t)), ?_⟩
    have hd : At (evFin F v) (u - (uT (GlobalTheory.LinBarAt.coAt G t u) + uM (-(u.map (piW t))))) := by
      intro c hc
      rw [smul_sub, smul_add, hu c hc, hTa _ c hc, hMa _ c hc, add_zero, sub_zero]
    refine (sub_eq_zero.1 (eq_zero_of_at σ hcm v t hd ?_ ?_))
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTt, hMt, neg_neg, zero_add, sub_self]
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTc, hMc, add_zero, hco, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
        Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, sub_self]
  · have h := GlobalTheory.T.local_lattice_hermitian_skew hcm v t G.V'.J G.W.J hTr.geo.hV'.herm hTr.geo.hW.skew x u hx
    dsimp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM] at h
    rw [hco, hco]
    exact h

end GlobalTheory.LinBarCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulSymplecticPairingCharacterTrivial
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct Topology

namespace GlobalTheory.FinCharInt

theorem tensInt_le {F E R : Type} [Field F] [CommRing E] [Algebra F E] [CommRing R] [Algebra F R]
    (S₁ : Subring E) (S₂ : Subring R) (K : AddSubgroup (E ⊗[F] R))
    (hK : ∀ b ∈ S₁, ∀ α ∈ S₂, b ⊗ₜ[F] α ∈ K) {x : E ⊗[F] R} (hx : x ∈ Formalism.UG.tensInt R S₁ S₂) : x ∈ K := by
  let C : AddSubgroup (E ⊗[F] R) := AddSubgroup.closure {z | ∃ b ∈ S₁, ∃ α ∈ S₂, z = b ⊗ₜ[F] α}
  have hC : C ≤ K := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, α, hα, rfl⟩
    exact hK b hb α hα
  have hmul : ∀ x ∈ C, ∀ y ∈ C, x * y ∈ C := by
    intro x hx y hy
    induction hx, hy using AddSubgroup.closure_induction₂ with
    | mem x y hx hy =>
      obtain ⟨b, hb, α, hα, rfl⟩ := hx
      obtain ⟨c, hc, β, hβ, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, S₁.mul_mem hb hc, _, S₂.mul_mem hα hβ, rfl⟩
    | zero_left x _ => rw [zero_mul]; exact C.zero_mem
    | zero_right x _ => rw [mul_zero]; exact C.zero_mem
    | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact C.add_mem h1 h2
    | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact C.add_mem h1 h2
    | neg_left x y _ _ h => rw [neg_mul]; exact C.neg_mem h
    | neg_right x y _ _ h => rw [mul_neg]; exact C.neg_mem h
  refine hC ?_
  unfold Formalism.UG.tensInt at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, c.2, _, S₂.one_mem, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, S₁.one_mem, _, c.2, rfl⟩
  | zero => exact C.zero_mem
  | one => exact AddSubgroup.subset_closure ⟨_, S₁.one_mem, _, S₂.one_mem, Algebra.TensorProduct.one_def⟩
  | add x y _ _ ihx ihy => exact C.add_mem ihx ihy
  | neg x _ ihx => exact C.neg_mem ihx
  | mul x y _ _ ihx ihy => exact hmul _ ihx _ ihy

theorem exists_nsmul_kill {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (hn : ∀ x, ‖ψ x‖ = 1) {ι : Type} [Finite ι] (c : ι → AF F) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∀ α ∈ Formalism.UG.intAd F, ψ (N • (pairA F 0 α * c i)) = 1 := by
  have hU : (⋂ i, {α : Af F | ψ (pairA F 0 (α * (c i).2)) = 1}) ∈ 𝓝 (0 : Af F) := by
    refine Filter.iInter_mem.2 fun i => ?_
    have h1 : Continuous fun α : Af F => α * (c i).2 := continuous_id.mul continuous_const
    exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA F 0 a) = 1})
      (by rw [zero_mul]; exact GlobalTheory.FinTranslate.ker_mem_nhds hc hn)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hU
  refine ⟨N, hN, fun i α hα => ?_⟩
  have h1 : ψ (pairA F 0 ((N • α) * (c i).2)) = 1 := Set.mem_iInter.1 (h α hα) i
  have e : N • (pairA F 0 α * c i) = pairA F 0 ((N • α) * (c i).2) :=
    Prod.ext (show N • ((0 : Ainf F) * (c i).1) = 0 by rw [zero_mul, smul_zero])
      (show N • (α * (c i).2) = (N • α) * (c i).2 from (smul_mul_assoc N α _).symm)
  rw [e, h1]

def kerSub {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) : AddSubgroup A where
  carrier := {a | ψ a = 1}
  zero_mem' := ψ.map_zero_eq_one
  add_mem' {a b} ha hb := by
    have ha' : ψ a = 1 := ha
    have hb' : ψ b = 1 := hb
    show ψ (a + b) = 1
    rw [AddChar.map_add_eq_mul, ha', hb', one_mul]
  neg_mem' {a} ha := by
    have ha' : ψ a = 1 := ha
    show ψ (-a) = 1
    have := AddChar.map_add_eq_mul ψ a (-a)
    rw [add_neg_cancel, ψ.map_zero_eq_one, ha', one_mul] at this
    exact this.symm

variable {D : D7}

noncomputable def finIncl (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem finIncl_finPart {a : AE D} (h : infPart D a = 0) : finIncl D (finPart D a) = a := by
  have key : ∀ a : AE D, (1 - GlobalTheory.FinTranslate.eInf D) • a = finIncl D (finPart D a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add a b ha hb => rw [smul_add, ha, hb, RingHom.map_add (f := _), map_add (f := _)]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      have : (1 - GlobalTheory.FinTranslate.eInf D) • a =
          LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) (sndA D.host.F a) :=
        Prod.ext (show (1 - 1) * a.1 = 0 by rw [sub_self, zero_mul]) (show (1 - 0) * a.2 = a.2 by rw [sub_zero, one_mul])
      rw [this]
      rfl
  rw [← key, sub_smul, one_smul, GlobalTheory.FinTranslate.smul_eq_zero_of_inf h, sub_zero]

theorem exists_nsmul_kill_forms {ψ : AddChar (AF D.host.F) ℂ} (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    {ι : Type} [Finite ι] (lam : ι → (AE D →ₗ[AF D.host.F] AF D.host.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∀ a : AE D, infPart D a = 0 → GlobalTheory.BotClassDict.finQ D a ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D →
      ψ (N • lam i a) = 1 := by
  let w := RingOfIntegers.basis D.host.E
  obtain ⟨N, hN, h⟩ := exists_nsmul_kill hc hn
    (fun p : ι × Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) =>
      lam p.1 ((1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E (w p.2))))
  refine ⟨N, hN, fun i a ha hint => ?_⟩
  let g : D.host.E ⊗[D.host.F] Af D.host.F →+ AF D.host.F :=
    N • ((lam i).toAddMonoidHom.comp ((finIncl D).toAddMonoidHom.comp
      (TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toLinearMap.toAddMonoidHom))
  have hg : ∀ y, g (Lev.swapAE D y) = N • lam i (finIncl D y) := by
    intro y
    have : TensorProduct.comm D.host.F D.host.E (Af D.host.F) (Lev.swapAE D y) = y :=
      (TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply y
    show N • lam i (finIncl D (TensorProduct.comm D.host.F D.host.E (Af D.host.F) (Lev.swapAE D y))) = _
    rw [this]
  have h1 : Lev.swapAE D (finPart D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have := (GlobalTheory.BotClassDict.toAfE_int_iff _).2 hint
    rwa [GlobalTheory.BotClassDict.toAfE_finQ] at this
  have h2 : Lev.swapAE D (finPart D a) ∈ (kerSub ψ).comap g := by
    refine tensInt_le _ _ _ ?_ h1
    rintro _ ⟨b, rfl⟩ α hα
    let φ : 𝓞 D.host.E →+ D.host.E ⊗[D.host.F] Af D.host.F :=
      ((TensorProduct.mk D.host.F D.host.E (Af D.host.F)).flip α).toAddMonoidHom.comp
        (algebraMap (𝓞 D.host.E) D.host.E).toAddMonoidHom
    have hb : b ∈ (((kerSub ψ).comap g).comap φ).toIntSubmodule := by
      have hsp : b ∈ Submodule.span ℤ (Set.range w) := by rw [w.span_eq]; trivial
      refine Submodule.span_le.2 ?_ hsp
      rintro _ ⟨k, rfl⟩
      have h3 := h (i, k) α hα
      rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h3
      exact h3
    exact hb
  have h3 : ψ (g (Lev.swapAE D (finPart D a))) = 1 := h2
  rwa [hg, finIncl_finPart ha] at h3

noncomputable def symplR (S T : HSp D) (x : WO S T) : WO S T →ₗ[AF D.host.F] AF D.host.F where
  toFun := symplOH S T x
  map_add' := GlobalTheory.FinTranslate.symplOH_add_right S T x
  map_smul' c y := GlobalTheory.FinTranslate.symplOH_smul_right S T c x y

theorem char_sympl_nsmul_int : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
    ∀ (S T : HSp D) (A0 : WO S T), ∃ N : ℕ, 0 < N ∧ ∀ v : WO S T, (∀ i j, infPart D (v i j) = 0) →
      (∀ i j, GlobalTheory.BotClassDict.finQ D (v i j) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D) → ψ (symplOH S T A0 (N • v)) = 1 := by
  intro D ψ hc hn S T A0
  obtain ⟨N, hN, h⟩ := exists_nsmul_kill_forms hc hn
    (fun p : Fin T.rank × Fin S.rank => (symplR S T A0).comp (Matrix.singleLinearMap (AF D.host.F) p.1 p.2))
  refine ⟨N, hN, fun v hv hint => ?_⟩
  show symplR S T A0 (N • v) ∈ kerSub ψ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_nsmul, Matrix.matrix_eq_sum_single v, map_sum, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  exact sum_mem fun j _ => h (i, j) (v i j) (hv i j) (hint i j)

end GlobalTheory.FinCharInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPointMemTensorLatticeIffIntegralCoordsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPoint_mem_tensorLattice_iff_integral_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E)),
    IsFrameAt w X.L A → IsFrameAt w Y.L Bm → ∀ x,
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion E)) ↔
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x ∈ latAtV X Y v := by
  first | exact @GlobalTheory.InertLat.kap_mem_latAtV_iff | exact GlobalTheory.InertLat.kap_mem_latAtV_iff | (intros; apply GlobalTheory.InertLat.kap_mem_latAtV_iff <;> assumption)
end

