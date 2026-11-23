module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0016
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
public import Development.WeilBound.ThetaLifts.TowerModels.StabCpt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaTrCoDblBoxFunK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ComplexConjugate
noncomputable section
namespace GlobalTheory.DblThetaProd
theorem thetaTr_coDbl_boxFun_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro F E _ _ _ _ _ σ B hB hstd nS nT JT JA JB ξ hA κ _ co φ₁ _ φ₂ _
  have hψ : ∀ x, ‖B.ψ x‖ = 1 := hstd.1.2.1
  have hc : ∀ x, starRingEnd ℂ (B.ψ x) = B.ψ (-x) := fun x => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ x)]
  funext w
  rw [GlobalTheory.DblTargetDelta.deltaT_apply]
  have he : (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co).e w =
      (Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).1 (co.e (GlobalTheory.DblTargetDelta.botR w)).1,
        Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).2 (-(co.e (GlobalTheory.DblTargetDelta.botR w)).2)) := rfl
  have hn : co.e (-GlobalTheory.DblTargetDelta.botR w) = -(co.e (GlobalTheory.DblTargetDelta.botR w)) := map_neg _ _
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, he, hn]
  generalize co.e (GlobalTheory.DblTargetDelta.topR w) = p₁
  generalize co.e (GlobalTheory.DblTargetDelta.botR w) = p₂
  obtain ⟨x₁, y₁⟩ := p₁
  obtain ⟨x₂, y₂⟩ := p₂
  simp only
  set A : (κ → F) → (κ → AdeleRing (𝓞 F) F) := fun b i => algebraMap F (AdeleRing (𝓞 F) F) (b i) with hAdef
  have key : ∀ q : (κ → F) × (κ → F),
      schr B.ψ (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) (boxFun φ₁ φ₂)
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm q i)) =
        schr B.ψ (x₁, y₁) φ₁ (A q.1) *
          (B.ψ (-(A q.2 ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A q.2 + x₂)) := by
    rintro ⟨a, b⟩
    have h1 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inl = A a + x₁ := by
      funext i; simp [hAdef]
    have h2 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inr = A b + x₂ := by
      funext i; simp [hAdef]
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun]
    rw [h1, h2, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr, hAdef]
    ring
  rw [← (Equiv.sumArrowEquivProdArrow κ κ F).symm.tsum_eq]
  refine (tsum_congr key).trans ?_
  refine (tsum_prod_mul (fun a => schr B.ψ (x₁, y₁) φ₁ (A a))
    (fun b => B.ψ (-(A b ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A b + x₂))).trans ?_
  congr 1
  rw [Complex.conj_tsum]
  conv_rhs => rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun b => ?_
  have h3 : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.neg (κ → F)) b i)) = -A b := by
    funext i; simp [hAdef]
  simp only [GlobalTheory.WeilM.schr, h3, map_mul, Complex.conj_conj, hc,
    Prod.fst_neg, Prod.snd_neg]
  simp only [neg_dotProduct, dotProduct_neg, neg_neg, neg_add, sub_eq_add_neg, mul_neg]
end GlobalTheory.DblThetaProd
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaTrLevelFK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.ThetaLevelF
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
set_option maxHeartbeats 1000000 in
theorem thetaTr_levelF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  obtain ⟨K, hK⟩ := GlobalTheory.ThetaLevel.schr_fin_fix F B.ψ hψ.1.1 Φ hΦ
  have hcont : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  let f1 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).1 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  let f2 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).2 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  have hf1 : Continuous f1 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hcont))
  have hf2 : Continuous f2 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hcont))
  let U : OpenAddSubgroup (WOF F E nS nT) := K.comap f1 hf1 ⊓ K.comap f2 hf2
  refine ⟨(U : AddSubgroup _), U.isOpen, fun u hu hinf => funext fun w => ?_⟩
  have hfix : GlobalTheory.WeilM.schr B.ψ (co.e u) Φ = Φ := by
    rw [e_eq_fin co u hinf]
    exact hK _ hu.1 _ hu.2
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e (w + u)) Φ) =
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e w) Φ)
  rw [map_add (f := _)]
  have h1 : GlobalTheory.WeilM.schr B.ψ (co.e w + co.e u) Φ = fun x =>
      B.ψ (-(⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2))) *
        GlobalTheory.WeilM.schr B.ψ (co.e w) (GlobalTheory.WeilM.schr B.ψ (co.e u) Φ) x :=
    funext (GlobalTheory.ThetaLevel.schr_add B.ψ _ _ Φ)
  rw [h1, hfix]
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have h2 : symplOHF σ JS JT ξ₀ w u =
      ⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2) := by
    rw [symplOHF, GlobalTheory.TransportF.symplOF_eq_symp hA hB, co.form]
    congr 1
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [h2, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
end GlobalTheory.ThetaLevelF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Bad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
variable {Y : Spc F E n} {B : Base F E} {v : Pl F} {r s : ℕ}
theorem theta_pm_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) : Y.θ w = 1 ∨ Y.θ w = -1 :=
  cartan_pm (h.sig w) h0 (fun i j => (hB.cm.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))) (h.cartan w)
theorem commute_theta_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) (A) : Commute A (Y.θ w) := by
  rcases _root_.GlobalTheory.ThK.Dbl.Bad.theta_pm_k hB h h0 w with e | e <;> rw [e]
  exacts [Commute.one_right _, Commute.neg_one_right _]
theorem stab_iff_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (UA σ Y.J)} (hK : IsStab B K)
    {g : UA σ Y.J} : g ∈ K ↔ ∀ v, IntAt v g :=
  (hK g).trans ⟨fun a _ z hz _ => a.2 z hz, fun a => ⟨fun w => _root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _, fun _ hz =>
    ⟨mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).1) hz, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).2) hz⟩⟩⟩
theorem emb_mem_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K)
    {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : ∀ v, IntAt v g) :
    e (g, 1) ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k hk => ?_⟩
  · rw [he g 1, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
    simp only [Commute, SemiconjBy, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (_root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _).eq, (_root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _).neg_right.eq]
  · obtain ⟨g', e1, hg'⟩ : ∃ g', k = e (g', 1) ∧ mat g' *ᵥ z ∈ latHat Y := by
      rcases hk with rfl | rfl
      · exact ⟨g, rfl, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).1) hz⟩
      · exact ⟨g⁻¹, by rw [← map_inv, Prod.inv_mk, inv_one], mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).2) hz⟩
    rw [e1, he g' 1, Matrix.fromBlocks_mulVec, show mat (1 : UA σ Y.J) = 1 from rfl]
    simpa using ⟨hg', hz'⟩
end GlobalTheory.ThK.Dbl.Bad
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadStmt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
def VacFix2_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ → ∀ χ : Chr F E, IsHecke F E χ → ∀ dd om, IsDblCoordX M dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χ (diagCols (Fin n)) om →
    ∀ K, IsStab2 (σ := σ) (Y := X) B K → ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
      Acts (evFin F v) (om k) (boxFun (M.vac v) (star (M.vac v))) (boxFun (M.vac v) (star (M.vac v)))
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def HgtEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h'))
def Unfold0_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 →
    ∀ (χ : Chr F E) (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsHecke F E χ → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ (f Ê : G2 σ Y → ℂ) (z : ℂ), Continuous f → Continuous Ê → (∀ x, HasSum (eisTerm f x) (Ê x)) →
      (∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x) →
    ∀ (μ : Measure (UA σ Y.J)) (D : Set (UA σ Y.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ Y.J) D μ →
      Integrable (fun g => f (e (1, g))) μ → ∀ φ : UA σ Y.J → ℂ, IsRapid φ → ∀ h,
        ∫ h' in D, Ê (e (h, h')) * detInv χ h' * φ h' ∂μ = ∫ g, f (e (1, g)) * detInv χ g * φ (h * g) ∂μ
def HgtInt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K a (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → IsHgt K a → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ μ : Measure (UA σ Y.J), μ.IsHaarMeasure → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def FinLevel_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (K : Subgroup (G2 σ Y)),
    IsCompact (K : Set (G2 σ Y)) → ∀ Φ ∈ schA F κ, ∃ Λ : Set (Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      (∀ u ∈ Λ, (∀ i, evI F ((dd.e u).1 i) = 0) ∧ (∀ i, evI F ((dd.e u).2 i) = 0) ∧ ∀ k ∈ K, actB (cA σ) k u ∈ Λ) ∧
      (∀ u ∈ Λ, dd.rho B.ψ u Φ = Φ) ∧ ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧
        ∀ Ψ : (κ → AF F) → ℂ, (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) → ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) →
          ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseUnfoldB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem aniso_of_k {B : Base F E} {r s : ℕ} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (h0 : min r s = 0) :
    Aniso σ Y.J := fun x hx => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have e : ((B.emb w).1 ∘ x) ⬝ᵥ Y.J.map (B.emb w).1 *ᵥ star ((B.emb w).1 ∘ x) = 0 := by
    rw [← map_zero (B.emb w).1, ← hx]
    simp [form, Matrix.mulVec, dotProduct, hB.cm.2.2.2]
  have : (B.emb w).1 ∘ x = 0 := hY.elim (fun h => HasSig.aniso (h.sig w) h0 e) fun h => HasSig.aniso (h.sig w) h0 (by
    rw [Matrix.smul_mulVec, dotProduct_smul, e, smul_zero])
  exact funext fun i => (map_eq_zero _).1 (congrFun this i)
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowStabCpt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKG.Tow.Stab
open scoped TensorProduct Matrix Pointwise RestrictedProduct
open NumberField IsDedekindDomain Topology Filter GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
attribute [local instance] ae_ring ae_t2 ae_smul
theorem exists_compact_mat_k {B : Base F E} {X : Spc F E n} {r s : ℕ} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hX : X.IsHerm σ B r s) :
    ∃ S : Set (Matrix (Fin n) (Fin n) (AE F E)), IsCompact S ∧ ∀ k ∈ stabK (σ := σ) B X, mat k ∈ S := by
  obtain ⟨Φ, hΦ, eΦ⟩ := exists_section hB.cm B.emb
  choose C hC h using fin_bound X hX.lat
  choose R hR using fun w => cartan_bound (hX.cartan w)
  have hD : IsCompact (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) :=
    (isCompact_univ_pi fun w => isCompact_closedBall _ _).image hΦ
  refine ⟨Set.univ.pi fun i => Set.univ.pi fun j => (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) + C i j,
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => hD.add (hC i j), fun k hk i _ j _ => ?_⟩
  rw [eΦ (mat k i j)]
  refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ (h i j _ fun y hy => (hk.2 y hy).1)
  rw [mem_closedBall_zero_iff]
  refine hR w ((mat k).map (piInf (B.emb w))) ?_ (hk.1 w) i j
  rw [← Levi.iso_map_piInf (σ := σ) (fun τ z => Levi.piInf_cA hB.cm τ z)]
  have e : (mat k)ᵀ * incM F X.J * (mat k).map (cA σ) = incM F X.J := k.2
  rw [e]
  exact Matrix.ext fun i j => Levi.piInf_incl _ _
theorem isCompact_stabK_k {B : Base F E} {X : Spc F E n} {r s : ℕ} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hX : X.IsHerm σ B r s) :
    IsCompact ((stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  obtain ⟨S, hS, h⟩ := _root_.PositivityTheory.ThKG.Tow.Stab.exists_compact_mat_k hB hX
  have hc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have hU : IsClosed ((UG (cA σ) (incM F X.J) : Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)) continuous_const
  exact isCompact_of_units _ hU _ (isClosed_stabK B X (isCompact_latHat X hX.lat.fg).isClosed) S hS
    fun k hk => ⟨h k hk, h _ (inv_mem hk)⟩
end PositivityTheory.ThKG.Tow.Stab
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnitEqMulConjK
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
theorem unit_eq_mul_conj_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∀ u : Fv F v, Valued.v u = 1 →
      ∃ z : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) u = z * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ z := by
  intro F E _ _ _ _ _ σ B hB v w hvw _hfield u hu
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hconj, hroot⟩ := exists_integral_gen σ hB.cm v hp
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨x, y, hxy⟩ := exists_int_sol v b c h2 hroot ⟨u, hu.le⟩ hu
  have hK : (x : Fv F v) ^ 2 - algebraMap F (Fv F v) (b : F) * x * y +
      algebraMap F (Fv F v) (c : F) * y ^ 2 = u := by
    have := congrArg (fun t : v.adicCompletionIntegers F => (t : v.adicCompletion F)) hxy
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow, coe_algebraMap_adicCompletionIntegers] at this
    exact this
  let ι := algebraMap (Fv F v) (Fv F v ⊗[F] E)
  have hιF : ∀ t : F, ι (algebraMap F (Fv F v) t) = (1 : Fv F v) ⊗ₜ[F] algebraMap F E t := fun t => by
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  set α : Fv F v ⊗[F] E := (1 : Fv F v) ⊗ₜ[F] (a : E) with hα
  have hq' : α ^ 2 + ι (algebraMap F (Fv F v) (b : F)) * α + ι (algebraMap F (Fv F v) (c : F)) = 0 := by
    have := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E) hq
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, map_zero] at this
    rw [hιF, hιF]
    exact this
  have hσα : Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ α =
      -ι (algebraMap F (Fv F v) (b : F)) - α := by
    rw [hα, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hconj, hιF,
      TensorProduct.tmul_sub, TensorProduct.tmul_neg]
  refine ⟨ι x + ι y * α, ?_⟩
  rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσα]
  have hKι := congrArg ι hK
  simp only [map_add (f := _), map_sub, map_mul, map_pow] at hKι
  linear_combination (-1 : Fv F v ⊗[F] E) * hKι + ι y ^ 2 * hq'
end GlobalTheory.InertUnitNorm
end
end

