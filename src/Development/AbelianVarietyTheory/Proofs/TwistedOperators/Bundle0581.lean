module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlancherelSchrodingerIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaAtEqProdAhG
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOrientedModelEqOfRealAdelicPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqProductDatumThetaConjugateHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.PlancherelHalf

theorem symplO_add_left {D : D7} (S T : HSp D) (t k y : WO S T) :
    symplO S T (t + k) y = symplO S T t y + symplO S T k y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem heisO_lin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (a : ℂ) (f₁ f₂ : WO S T → ℂ) :
    heisO ψ S T w (a • f₁ + f₂) = a • heisO ψ S T w f₁ + heisO ψ S T w f₂ := by
  funext x; simp only [heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem ipO_self {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m n → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 f f = ((nrm2 μ 𝓕 f : ℝ) : ℂ) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO nrm2
  rw [← integral_complex_ofReal]
  congr 1; funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem ipO_conj {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f g : Mx D m n → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 g f = starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 f g) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO
  rw [← integral_conj]
  congr 1; funext w; simp [mul_comm]

theorem ipO_lin {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a : ℂ) (f₁ f₂ g : Mx D m n → ℂ)
    (h₁ : IntegrableOn (fun w => f₁ w * (starRingEnd ℂ) (g w)) 𝓕 μ)
    (h₂ : IntegrableOn (fun w => f₂ w * (starRingEnd ℂ) (g w)) 𝓕 μ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (a • f₁ + f₂) g = a * GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 f₁ g + GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 f₂ g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO
  rw [← integral_const_mul, ← integral_add (h₁.const_mul a) h₂]
  congr 1; funext w; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem norm_sq_product_extension_matrix_family_sum {ι : Type} (S : Finset ι) (κ : ι → Type) [∀ i, Fintype (κ i)] (a b : ℕ)
    (ext : (∀ i : ↥S, Matrix (Fin a) (Fin b) (κ i.1)) → ∀ i, Matrix (Fin a) (Fin b) (κ i))
    (hext : ∀ z (i : ↥S), ext z i.1 = z i)
    (Gd : (∀ i, Matrix (Fin a) (Fin b) (κ i)) → ℂ) (h : ∀ i, Matrix (Fin a) (Fin b) (κ i) → ℝ)
    (hGd : ∀ y, ‖Gd y‖ = ∏ i ∈ S, h i (y i)) :
    (∑ z : (∀ i : ↥S, Matrix (Fin a) (Fin b) (κ i.1)), ‖Gd (ext z)‖ ^ 2) /
        (Fintype.card (∀ i : ↥S, Matrix (Fin a) (Fin b) (κ i.1)) : ℝ) =
      ∏ i ∈ S, (∑ᶠ z, h i z ^ 2) / (Nat.card (κ i) : ℝ) ^ (a * b) := by
  have h1 : ∀ z : (∀ i : ↥S, Matrix (Fin a) (Fin b) (κ i.1)), ‖Gd (ext z)‖ ^ 2 = ∏ i : ↥S, h i.1 (z i) ^ 2 := by
    intro z
    rw [hGd, ← Finset.prod_pow, ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun i _ => by rw [hext]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (i : ↥S) (m : Matrix (Fin a) (Fin b) (κ i.1)) => h i.1 m ^ 2), Fintype.card_pi, ← Finset.prod_coe_sort S, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  congr 1
  rw [show Fintype.card (Matrix (Fin a) (Fin b) (κ i.1)) = Fintype.card (Fin a → Fin b → κ i.1) from rfl, Fintype.card_fun, Fintype.card_fun]
  simp [← pow_mul, mul_comm]

theorem normSq_thetaAt_halfProd : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io →
  ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) →
  ∀ (Gd : (∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) → ℂ)
    (h : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP) → ℝ),
    (∀ y, ‖Gd y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, h PP (y PP)) →
  ∀ f' : WO (Vc D i) (Wc D i) → ℂ,
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e)
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 f₀
      (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        Gd (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) f' →
  ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    nrm2 μ 𝓧 f' = ∏ PP ∈ R.Pg ∪ R.Q t, (∑ᶠ z, h PP z ^ 2) / (Nat.card (kP PP) : ℝ) ^ ((Vc D i).rank * (Wc D i).rank) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he Gd h hGd f' hθ μ 𝓧 hcov

  have hW := hL.2.2.2.2.2.1
  have hLV := hL.2.2.2.2.2.2.2.1
  have hvac := hLV.1.2
  have hU := (hPM.1 R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hW).2 (μ, 𝓧) hcov
  have hf₀n : nrm2 μ 𝓧 f₀ = 1 := hvac.norm.2 (μ, 𝓧) hcov
  set S := R.Pg ∪ R.Q t with hS
  set Λ := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) with hΛ
  let FM := frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i)
  have hlat := _root_.GlobalTheory.HalfLatFrames.halfLat_iff_isIntM R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he
  let Λc : AddSubgroup (WO (Vc D i) (Wc D i)) :=
    { carrier := {x | x ∈ Λ ∧ IsHalf (cA D e) x}
      add_mem' := fun {a b} ha hb => ⟨Λ.add_mem ha.1 hb.1, fun p q => by
        simp only [Matrix.add_apply, mul_add, ha.2 p q, hb.2 p q]⟩
      zero_mem' := ⟨Λ.zero_mem, fun p q => by simp⟩
      neg_mem' := fun {a} ha => ⟨Λ.neg_mem ha.1, fun p q => by
        simp only [Matrix.neg_apply, mul_neg, ha.2 p q]⟩ }
  have hmem : ∀ x, x ∈ Λc ↔ IsHalf (cA D e) x ∧ IsIntM (FM x) := fun x =>
    ⟨fun hx => ⟨hx.2, (hlat x hx.2).1 hx.1⟩, fun hx => ⟨(hlat x hx.1).2 hx.2, hx.1⟩⟩
  haveI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP =>
    @Fintype.ofFinite _ (Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot)
  let Gt := ∀ PP : ↥S, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP.1)
  let red : Λc →+ Gt := AddMonoidHom.mk' (fun x PP => redM PP.1 (FM x.1)) (fun x y => by
    funext PP
    exact (_root_.GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM (Vc D i) (Wc D i) (R.βV i) (R.βW i) x.1 y.1 ((hmem _).1 x.2).2 ((hmem _).1 y.2).2).2 PP.1)
  let ext : Gt → ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP) :=
    fun z PP => if hP : PP ∈ S then z ⟨PP, hP⟩ else 0
  obtain ⟨Tm, hTm⟩ := hθ.1
  have hf' := hθ.2 Tm hTm

  have hΦ : (fun x => if IsHalf (cA D e) x ∧ IsIntM (FM x) then Gd (fun PP => redM PP (FM x)) else 0) =
      fun x => if hx : x ∈ Λc then Gd (ext (red ⟨x, hx⟩)) else 0 := by
    funext x
    by_cases hx : IsHalf (cA D e) x ∧ IsIntM (FM x)
    · have hx' : x ∈ Λc := (hmem x).2 hx
      rw [if_pos hx, dif_pos hx']
      congr 1; funext PP
      by_cases hP : PP ∈ S
      · simp only [ext, dif_pos hP]; rfl
      · simp only [ext, dif_neg hP]
        exact _root_.GlobalTheory.AdjRedOff.redM_frMapAdj_off R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he x hx.1 hx.2 PP hP
    · have hx' : x ∉ Λc := fun h' => hx ((hmem x).1 h')
      rw [if_neg hx, dif_neg hx']
  have key := _root_.GlobalTheory.finite_plancherel_schrodinger_intertwiner R.ψ (symplO (Vc D i) (Wc D i)) Λc red Tm (heisO R.ψ (Vc D i) (Wc D i))
    (IsSBHalf (cA D e) Λ) (IsHalf (cA D (cA D e))) (IsThetaFunO R.ψ (Vc D i) (Wc D i))
    (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓧) f₀ (fun z => Gd (ext z))
    (by
      intro z
      obtain ⟨x, hx1, hx2, hx3⟩ := _root_.GlobalTheory.AdjRedOnto.exists_half_redM_eq R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he (ext z)
      refine ⟨⟨x, (hmem x).2 ⟨hx1, hx2⟩⟩, ?_⟩
      funext PP
      show redM PP.1 (FM x) = z PP
      rw [hx3 PP.1 PP.2]; simp only [ext, dif_pos PP.2])
    (symplO_add_left _ _)
    (by
      intro Ψ hsupp hinv
      refine ⟨fun t ht => (hsupp t ht).2, Fintype.card Gt, Fintype.card_pos, fun u hu hh t => hinv t u ⟨hu, hh⟩,
        fun t ht => ?_⟩
      exact Λ.nsmul_mem (hsupp t ht).1 _)
    (fun Φ hΦ x hx => hTm.trans Φ hΦ x hx.2)
    (fun Φ hΦ y hy => hTm.modul Φ hΦ y hy)
    (by
      have := hTm.vac
      rw [one_smul] at this
      rw [← this]
      congr 1
      funext x
      unfold halfInd
      by_cases hx : x ∈ Λ ∧ IsHalf (cA D e) x
      · rw [if_pos (show x ∈ Λc from hx), if_pos hx]
      · rw [if_neg (show x ∉ Λc from hx), if_neg hx])
    (by
      intro x hx
      have hx2 := (hmem _).1 x.2
      obtain ⟨PP, hPP⟩ : ∃ PP : ↥S, redM PP.1 (FM x.1) ≠ 0 := by
        by_contra hc; push_neg at hc; exact hx (funext hc)
      obtain ⟨y, hy1, hy2, hy3⟩ := _root_.GlobalTheory.HalfDuality.exists_dual_half R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he x.1 hx2.1 hx2.2
        ⟨PP.1, PP.2, hPP⟩
      refine ⟨y, hy1, fun k hk => ?_, hy3⟩
      have hk2 := (hmem _).1 k.2
      exact hy2 k.1 hk2.1 hk2.2 fun PP hP => congrFun hk ⟨PP, hP⟩)
    (heisO_lin R.ψ (Vc D i) (Wc D i))
    (fun a f₁ f₂ h₁ h₂ => (hU f₁ f₂ h₁ h₂).1 a)
    (fun w f hf => ((hU f f hf hf).2.2.2.2.1 w).1)
    (fun a f₁ f₂ g h₁ h₂ hg => ipO_lin μ 𝓧 a f₁ f₂ g (hU f₁ g h₁ hg).2.1 (hU f₂ g h₂ hg).2.1)
    (fun f g _ _ => ipO_conj μ 𝓧 f g)
    (fun w f₁ f₂ h₁ h₂ => ((hU f₁ f₂ h₁ h₂).2.2.2.2.1 w).2)
    hvac.theta
    (by rw [ipO_self, hf₀n]; simp)
  rw [← hΦ, ← hf'] at key
  have hn : nrm2 μ 𝓧 f' = (∑ z : Gt, ‖Gd (ext z)‖ ^ 2) / (Fintype.card Gt : ℝ) := by
    have := congrArg Complex.re key
    rw [ipO_self, Complex.ofReal_re] at this
    rw [this]
    have h2 : ((∑ z : Gt, ‖Gd (ext z)‖ ^ 2 : ℝ) : ℂ) / (Fintype.card Gt : ℂ) =
        (((∑ z : Gt, ‖Gd (ext z)‖ ^ 2) / (Fintype.card Gt : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.ofReal_re]
  rw [hn]
  exact norm_sq_product_extension_matrix_family_sum S (fun PP => kP PP) _ _ ext (fun z PP => by simp only [ext, dif_pos PP.2]) Gd h hGd

end GlobalTheory.PlancherelHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiRealPtEqExpIm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem modelW_of_tieIn {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (h : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) :
    ∀ k, ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) := by
  subst hσ
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, hk⟩ := h.laws.modelW _ hj T.σ₀ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (_ : V = Wc D i) (hr' : V.rank = D.R.r) (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r),
      ModelW V hr' X → ModelW (Wc D i) (rank_Wc i) X := by
    rintro V rfl hr' X hX
    exact hX
  exact fun k => key _ hV hr _ (hk k)

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.FinTranslate

theorem heis_law_of_periods : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.IsThP → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (ph : ℂ)
    (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), IsONLatBasis (Vc D i) b →
    (∀ k, ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k)) →
    ∀ (γ g : GA D (Wc D i)) (hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩) (Y : UnitAt Wt),
      PinAt T R i σ hV ph b γ g hx Wt Y →
    ∀ Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E, (∀ a, perVec Wt (colB b Yr a) ∈ Set.range Wt.Pm) →
      heisO R.ψ (Vc D i) (Wc D i) (-(ratW (Wc D i) (Vc D i) Yr - realPt (Vc D i) (Wc D i) Yr))
          (R.ωP i A.μ0 (1, γ * g) (R.vacP i)) =
        (∏ a, Y.χl (perVec Wt (colB b Yr a))) • R.ωP i A.μ0 (1, γ * g) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A T _ R hT i σ hV ph b hb hM γ g hx Wt Y hp Yr hcol
  have hW := hT.ωP i A.μ0
  have hv := hT.vP i A.μ0
  have hψ : IsStdChar D R.ψ (-1) := hW.std
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hv.1.2.theta
  set Θ := R.ωP i A.μ0 (1, γ * g) (R.vacP i) with hΘdef
  have hΘ : IsThetaFunO R.ψ (Vc D i) (Wc D i) Θ := hW.om_pres _ _ hf
  choose α hα using hcol
  refine _root_.GlobalTheory.ThetaUniqReal.eq_of_eq_realPt D R.ψ hψ (Vc D i) (Wc D i) _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΘ _)
    (theta_smul _ hΘ) fun X => ?_
  have hth : ∀ w, thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * g) w = Θ w := fun w => thetaAt_eq _ _ _ _ _
  have e1 := theta_realPt_add hΘ X Yr
  have e2 := thetaAt_eq_prod_ahG hp (X + Yr)
  have e3 := thetaAt_eq_prod_ahG hp X
  rw [hth] at e2 e3
  have hcolAdd : ∀ a, perVec Wt (colB b (X + Yr) a) = pv Wt (colB b X a) + Wt.Pm (α a) := fun a => by
    rw [hα a]
    have : colB b (X + Yr) a = colB b X a + colB b Yr a := by
      funext m; simp only [colB, Matrix.add_apply, add_mul, Finset.sum_add_distrib, Pi.add_apply]
    rw [this]
    exact (pvHom Wt).map_add _ _
  have hG : ∀ a, ahG Y (perVec Wt (colB b (X + Yr) a)) = Y.χl (perVec Wt (colB b Yr a)) *
      Complex.exp (Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E (-((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).ξ0 *
        ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).Gm (colB b X a) (colB b Yr a)) : ℚ) : ℂ)) *
      ahG Y (perVec Wt (colB b X a)) := fun a => by
    rw [hcolAdd a, ahG_add_period, hα a]
    have him := im_hermForm_pv Wt Y (colB b X a) (colB b Yr a)
    change _ * Complex.exp (_ * ((hermForm Y.Hm (pv Wt (colB b X a)) (pv Wt (colB b Yr a))).im : ℂ)) * _ = _
    rw [him]
    push_cast
    rfl
  have hL : R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)) =
      Complex.exp (Real.pi * Complex.I * ∑ a, ((Algebra.trace ℚ D.host.E
        (-((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).ξ0 *
        ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).Gm (colB b X a) (colB b Yr a)) : ℚ) : ℂ)) :=
    _root_.GlobalTheory.ArchPhase.psi_symplOH_realPt D R.ψ hψ (Vc D i) (Wc D i) b hb D.R.r (rank_Wc i) _ (hM (dictW T i σ hV g).1) X Yr
  have hs : R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)) ≠ 0 := by
    intro h0
    have := AddChar.map_add_eq_mul R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr))
      (-(symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  have key : Θ (realPt (Vc D i) (Wc D i) (X + Yr)) = R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X)
      (realPt (Vc D i) (Wc D i) Yr)) * ((∏ a, Y.χl (perVec Wt (colB b Yr a))) * Θ (realPt (Vc D i) (Wc D i) X)) := by
    rw [e2, e3, hL, Finset.prod_congr rfl (fun a _ => hG a), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Complex.exp_sum, Finset.mul_sum]
    ring
  apply mul_left_cancel₀ hs
  rw [← e1, key, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem psi_realPt_eq_exp_im : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.IsThP → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), IsONLatBasis (Vc D i) b →
    (∀ k, ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k)) →
    ∀ (g : GA D (Wc D i)) (hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩) (Y : UnitAt Wt)
      (X Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E),
      R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)) =
        Complex.exp (Real.pi * Complex.I *
          ∑ a, ((hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b Yr a))).im : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R hT i σ hV b hb hM g hx Wt Y X Yr
  have hψ : IsStdChar D R.ψ (-1) := (hT.ωP i A.μ0).std
  rw [_root_.GlobalTheory.ArchPhase.psi_symplOH_realPt D R.ψ hψ (Vc D i) (Wc D i) b hb D.R.r (rank_Wc i) _ (hM (dictW T i σ hV g).1) X Yr]
  refine congrArg Complex.exp (congrArg (fun t => (Real.pi : ℂ) * Complex.I * t) (Finset.sum_congr rfl fun a _ => ?_))
  have h := im_hermForm_pv Wt Y (colB b X a) (colB b Yr a)
  change _ = (((hermForm Y.Hm (pv Wt (colB b X a)) (pv Wt (colB b Yr a))).im : ℝ) : ℂ)
  rw [h]
  push_cast
  rfl

theorem frame_phase : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (ph : ℂ)
    (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → IsONLatBasis (Vc D i) b →
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ g →
    ∀ (hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩)
      (Y : UnitAt Wt), PinAt T R i σ hV ph b γ g hx Wt Y →
    ∀ Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      ((∀ a, perVec Wt (colB b Yr a) ∈ Set.range Wt.Pm) ↔
        actO (Vc D i) (Wc D i) 1 (γ * g)⁻¹ (ratW (Wc D i) (Vc D i) Yr - realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) ∧
      ((∀ a, perVec Wt (colB b Yr a) ∈ Set.range Wt.Pm) →
        heisO R.ψ (Vc D i) (Wc D i) (-(ratW (Wc D i) (Vc D i) Yr - realPt (Vc D i) (Wc D i) Yr))
            (R.ωP i A.μ0 (1, γ * g) (R.vacP i)) =
          (∏ a, Y.χl (perVec Wt (colB b Yr a))) • R.ωP i A.μ0 (1, γ * g) (R.vacP i)) ∧
      ∀ X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
        R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)) =
          Complex.exp (Real.pi * Complex.I *
            ∑ a, ((hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b Yr a))).im : ℂ)) := by
  intro D hHP hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hL hGr hFa hMo hT hTie i σ hσ hV ph b hph hb γ hγ g hFr hx Wt Y hp Yr
  have hM := modelW_of_tieIn hTie i σ hσ hV
  exact ⟨_root_.GlobalTheory.AHPhase.cols_per_iff_latO D hHP hSL hVF G Pl0 T0 A T R F κ v₀ hL hGr hFa hMo hT hTie i σ hσ hV ph b hph hb γ hγ g hFr hx Wt Y
      hp Yr,
    heis_law_of_periods D G Pl0 T0 A T R hT i σ hV ph b hb hM γ g hx Wt Y hp Yr,
    fun X => psi_realPt_eq_exp_im D G Pl0 T0 A T R hT i σ hV b hb hM g hx Wt Y X Yr⟩

end GlobalTheory.AHPhase
end
end

