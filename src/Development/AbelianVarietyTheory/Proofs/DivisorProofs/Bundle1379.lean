module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Facts

theorem infPart_eq_one {D : D7} {v ε} (hε : IsPlaceIdem D v ε) {x : AE D}
    (hx : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem sigW_add {D : D7} (i : Fin D.R.m) :
    (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
  have := D.R.m_add_three_le_k
  have hi := i.2
  rw [rank_Wc i]
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem signs_of_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (ρ : D.what₂.Tau) (a : Fin (Wc D i).rank) :
    (R.MW i σ).ε ρ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
  have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have he := (R.MW i σ).enum ρ
  unfold Links.parAt at he
  rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
  exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs]; exact sigW_add i) he a).2

end GlobalTheory.GalOne.Facts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqArithmeticGroupMulScalarOfMovedFrames
section
noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevModel

theorem orbit_open_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (τ₀ : Ψ) (G : Subgroup (GL (Fin r) E)) (h : GL (Fin r) E) {O : Set (Frame Ψ r)} (hO : IsOpen O)
    (hne : O.Nonempty) (hdet : ∀ y ∈ O, (mat y τ₀).det ≠ 0)
    (H1 : ∀ y ∈ O, ∃ γ ∈ G, ∃ b ∈ Bor Ψ r, lact h y = rmul (lact γ y) b) :
    ∃ γ ∈ G, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ hy₀
  set B₀ := Metric.ball y₀ ρ with hB₀
  let f : Option G → Set (Frame Ψ r) := fun o => match o with
    | none => B₀ᶜ
    | some γ' => ReciprocityTheory.ChartRestriction.G.PullbackSections.TSet Ψ ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have hc : ∀ o, IsClosed (f o) := by
    rintro (_ | γ')
    · exact Metric.isOpen_ball.isClosed_compl
    · exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isClosed_TSet _ _
  have hU : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    by_cases hx : x ∈ B₀
    · obtain ⟨γ', hγ', b, hb, e⟩ := H1 x (hball hx)
      exact ⟨some ⟨γ', hγ'⟩, ReciprocityTheory.ChartRestriction.G.PullbackSections.mem_TSet Ψ h γ' hb e⟩
    · exact ⟨none, hx⟩
  have hd := dense_iUnion_interior_of_closed hc hU
  obtain ⟨y, hyB, hyU⟩ := hd.inter_open_nonempty B₀ Metric.isOpen_ball ⟨_, Metric.mem_ball_self hρ⟩
  obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hyU
  cases o with
  | none => exact absurd hyB (interior_subset ho)
  | some γ' =>
    set g : Matrix (Fin r) (Fin r) E := ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hg
    obtain ⟨κ, hκ⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.scalar_step τ₀ g
      (W := interior (f (some γ')) ∩ B₀) (isOpen_interior.inter Metric.isOpen_ball)
      (fun x hx => interior_subset hx.1) (y := y) ⟨ho, hyB⟩ (hdet y (hball hyB))
    have hent : ∀ a b, τ₀.1 (g a b) = if a = b then κ else 0 := by
      intro a b
      have := congrFun (congrFun hκ a) b
      simpa [Matrix.one_apply] using this
    have hh : (h : Matrix (Fin r) (Fin r) E) = (γ'.1 : Matrix (Fin r) (Fin r) E) * g := by
      rw [hg, ← Units.val_mul, mul_inv_cancel_left]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact ⟨γ'.1, γ'.2, 0, by ext a; exact Fin.elim0 a⟩
    · refine ⟨γ'.1, γ'.2, g ⟨0, hr⟩ ⟨0, hr⟩, ?_⟩
      rw [hh]
      congr 1
      ext a b
      apply τ₀.1.injective
      rw [hent a b, Matrix.scalar_apply, Matrix.diagonal_apply]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, hent, if_pos rfl]
      · rw [if_neg hab, if_neg hab, map_zero]

theorem eq_mul_scalar_of_moved {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ h : GL (Fin r) E) (hΨ : X₂.Ψ = X.Ψ)
    (H : ∀ x ∈ X₂.dom, ∀ x' : Frame X.Ψ r, GlobalTheory.LevModel.Moved X₂ X δ x x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact h x' = rmul (lact γ x') b) :
    ∃ γ ∈ X.Γ, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical

  obtain ⟨τ₁⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases hτ : τ₁ ∈ X.Ψ
    · exact ⟨τ₁, hτ⟩
    · refine ⟨ComplexEmbedding.conjugate τ₁, ?_⟩
      by_contra hc
      exact hτ ((X.cmType τ₁).2 hc)
  have hmem : ∀ τ : X₂.Ψ, τ.1 ∈ X.Ψ := fun τ => hΨ ▸ τ.2
  have hmem' : ∀ τ : X.Ψ, τ.1 ∈ X₂.Ψ := fun τ => hΨ.symm ▸ τ.2

  let back : Frame X.Ψ r → Frame X₂.Ψ r := fun y τ =>
    (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y ⟨τ.1, hmem τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  let fwd : Frame X₂.Ψ r → Frame X.Ψ r := fun x τ =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, hmem' τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  have hback : Continuous back := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hm : Continuous fun y : Frame X.Ψ r => mat y ⟨τ.1, hmem τ⟩ := continuous_apply _
    exact (continuous_const.matrix_mul hm).matrix_elem a b
  have hbf : ∀ x, back (fwd x) = x := by
    intro x
    funext τ
    show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Matrix.mul_assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul, Matrix.one_mul]
  have hmoved : ∀ y, GlobalTheory.LevModel.Moved X₂ X δ (back y) y := by
    intro y τ h₂ h₁
    show mat y ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ *
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * mat y ⟨τ, h₁⟩)
    rw [← Matrix.mul_assoc]
    have := ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul τ (δ⁻¹ : GL (Fin r) E)
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]
  have hdom : (X₂.dom).Nonempty := ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X₂ (ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.chosenFrame_isOrthogonal X₂)⟩
  obtain ⟨x₀, hx₀⟩ := hdom
  refine orbit_open_scalar ⟨τ₀, hτ₀⟩ X.Γ h (O := back ⁻¹' X₂.dom)
    ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X₂).preimage hback) ⟨fwd x₀, by rw [Set.mem_preimage, hbf]; exact hx₀⟩ ?_
    (fun y hy => H _ hy y (hmoved y))
  intro y hy
  have h1 := (hy ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩).1
  have h2 : mat (back y) ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩ =
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ₀ * mat y ⟨τ₀, hτ₀⟩ := rfl
  rw [h2, Matrix.det_mul] at h1
  exact right_ne_zero_of_mul h1

end GlobalTheory.LevModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqFinsetSumPureTensorCosetIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

theorem eq_sum_pureA_coset_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
    (K : Set (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact K →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
        (∀ r ∈ R, Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
          (∀ x, (fun i => (x i).2) ∉ K → Φ x = 0) →
            Φ = ∑ r ∈ R, GlobalTheory.WeilM.pureA F (GlobalTheory.WeilAdm.slice F Φ r) (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ U K hUo hUc hK
  classical
  have hcov : K ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ K, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  have hSB : ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    intro r
    have hcl : IsClopen {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      ⟨(AddSubgroup.isClosed_of_isOpen U hUo).preimage (continuous_id.sub continuous_const),
        hUo.preimage (continuous_id.sub continuous_const)⟩
    have hco : IsCompact {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      (Homeomorph.subRight r).isCompact_preimage.2 hUc
    refine ⟨?_, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U}
      · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_mem (show y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} from hy),
          Set.indicator_of_mem hx]
      · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
        simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)
  refine ⟨R, fun r _ => hSB r, fun Φ hinv hsupp => ?_⟩
  funext x
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, (fun i => (x i).2) - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have hm : (fun i => (x i).2) ∈ {y | y - r0 ∈ U} := hxr0
      simp only [GlobalTheory.WeilM.pureA, GlobalTheory.WeilAdm.slice, RingEquiv.symm_apply_apply, Set.indicator_of_mem hm, mul_one]
      obtain ⟨x', hx'⟩ : ∃ x' : κ → AdeleRing (𝓞 F) F, x' = fun i => ((x i).1, r0 i) := ⟨_, rfl⟩
      have e : x = x' + GlobalTheory.WeilAdm.finE F ((fun i => (x i).2) - r0) := by
        subst hx'
        funext i
        refine Prod.ext ?_ ?_
        · show (x i).1 = (x i).1 + 0
          rw [add_zero]
        · show (x i).2 = r0 i + ((x i).2 - r0 i)
          rw [add_sub_cancel]
      conv_lhs => rw [e]
      rw [hinv x' _ hxr0, hx']
    · intro r hr hne
      simp only [GlobalTheory.WeilM.pureA]
      have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : (fun i => (x i).2) ∉ K := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [hsupp x hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    simp only [GlobalTheory.WeilM.pureA]
    have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.WeilAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ArchTraceNondeg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro hM
  apply h2
  simp [Matrix.det_mul, hM]

theorem det_J_ne_zero {σ : E →ₐ[F] E} (B : Base F E) {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) :
    X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  have := RingHom.map_det (B.emb w).1 X.J
  rw [h0, map_zero] at this
  exact this.symm

theorem sigma_surjective (σ : E →ₐ[F] E) : Function.Surjective σ := by
  have hinj : Function.Injective ((σ : E →+* E).toRatAlgHom.toLinearMap) := (σ : E →+* E).injective
  exact LinearMap.injective_iff_surjective.1 hinj

def cAinv (σ : E →ₐ[F] E) : AE F E →ₐ[AF F] AE F E :=
  Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F))
    (AlgEquiv.ofBijective σ ⟨(σ : E →+* E).injective, sigma_surjective σ⟩).symm.toAlgHom

theorem cA_cAinv (σ : E →ₐ[F] E) (x : AE F E) : cA σ (cAinv σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp only [cAinv, cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    congr 1
    exact AlgEquiv.apply_symm_apply (AlgEquiv.ofBijective σ ⟨(σ : E →+* E).injective, sigma_surjective σ⟩) y
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem at_cAinv (σ : E →ₐ[F] E) {t : AE F E} (ht : At (evI F) t) : At (evI F) (cAinv σ t) := by
  intro u hu
  rw [← map_smul, ht u hu, map_zero]

theorem at_single {n : ℕ} (k : Fin n) {t : AE F E} (ht : At (evI F) t) :
    At (evI F) (Pi.single k t : Fin n → AE F E) := by
  intro u hu
  funext j
  by_cases hj : j = k
  · subst hj; simp [ht u hu]
  · simp [Pi.single_apply, hj]

theorem at_vecMul {n : ℕ} {b : Fin n → AE F E} (hb : At (evI F) b) (A : Matrix (Fin n) (Fin n) (AE F E)) (k : Fin n) :
    At (evI F) ((b ᵥ* A) k) := by
  intro u hu
  have h := hb u hu
  simp only [Matrix.vecMul, dotProduct, Finset.smul_sum, smul_mul_assoc]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← smul_mul_assoc]
  have : u • b i = 0 := by simpa using congrFun h i
  rw [this, zero_mul]

theorem eq_zero_of_trace_orth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n : ℕ} (X : Spc F E n) (r s : ℕ),
    (∀ β : AE F E, At (evI F) β → (∀ t : AE F E, At (evI F) t →
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) (β * t))) = 0) → β = 0) →
    X.IsHerm σ B r s → ∀ b : Fin n → AE F E, At (evI F) b →
    (∀ c : Fin n → AE F E, At (evI F) c → Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (evI F (Algebra.trace (AF F) (AE F E) (b ⬝ᵥ (incM F X.J *ᵥ fun k => cA σ (c k))))) = 0) → b = 0 := by
  intro F E _ _ _ _ _ σ B n X r s hβ hX b hb hc
  have hdet : IsUnit (incM F X.J).det := by
    have h : (incM F X.J).det = inclR (F := F) (AF F) X.J.det := by
      rw [RingHom.map_det]; rfl
    rw [h]
    exact (isUnit_iff_ne_zero.2 (det_J_ne_zero B hX)).map _
  have hv : b ᵥ* incM F X.J = 0 := by
    funext k
    apply hβ _ (at_vecMul hb _ k)
    intro t ht
    have h := hc (Pi.single k (cAinv σ t)) (at_single k (at_cAinv σ ht))
    rw [Matrix.dotProduct_mulVec] at h
    have hw : (fun j => cA σ ((Pi.single k (cAinv σ t) : Fin n → AE F E) j)) = Pi.single k t := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [cA_cAinv]
      · simp [Pi.single_apply, hj]
    rw [hw, dotProduct_single] at h
    exact h
  calc b = b ᵥ* (incM F X.J * (incM F X.J)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    _ = (b ᵥ* incM F X.J) ᵥ* (incM F X.J)⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [hv, Matrix.zero_vecMul]

end GlobalTheory.ArchTraceNondeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryConjOfCharpolyEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.IntUnitConj

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P.Separable →
    ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ y y' : UL n w, y ∈ KL n w → y' ∈ KL n w → y.1.val.charpoly = atPl w P →
      y'.1.val.charpoly = atPl w P → ∃ g ∈ KL n w, y' = g⁻¹ * y * g := by
  intro E _ _ _ hU n P hP
  filter_upwards [UnitInert.eventually_separable P hP] with w hsep γ γ' hγK hγ'K hγ hγ'
  let O := w.adicCompletionIntegers E
  let ι := algebraMap O (w.adicCompletion E)
  have hι : Function.Injective ι := Subtype.val_injective
  change γ.1 ∈ (GeneralLinearGroup.map ι).range at hγK
  change γ'.1 ∈ (GeneralLinearGroup.map ι).range at hγ'K
  obtain ⟨y', hy'⟩ := hγK
  obtain ⟨z', hz'⟩ := hγ'K
  have hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly := fun x =>
    (Matrix.charpoly_map _ _).symm
  have e1 : y'.val.charpoly.map ι = atPl w P := by rw [hch, hy', hγ]
  have e2 : z'.val.charpoly.map ι = atPl w P := by rw [hch, hz', hγ']
  have e12 : z'.val.charpoly = y'.val.charpoly := Polynomial.map_injective ι hι (e2.trans e1.symm)
  suffices H : ∃ u : GL (Fin n) O, GeneralLinearGroup.map ι u ∈ UL n w ∧ y'.val * u.val = u.val * z'.val by
    obtain ⟨u, hu, hcu⟩ := H
    let g : GLw n w := GeneralLinearGroup.map ι u
    have key : γ.1 * g = g * γ'.1 := by
      rw [← hy', ← hz', ← map_mul, ← map_mul]
      congr 1
      exact Units.ext hcu
    refine ⟨⟨g, hu⟩, Subgroup.mem_subgroupOf.2 ⟨u, rfl⟩, Subtype.ext ?_⟩
    change γ'.1 = g⁻¹ * γ.1 * g
    rw [mul_assoc, key, inv_mul_cancel_left]
  by_cases hw : IsSplitAt w
  · obtain ⟨u, hu⟩ := GlobalTheory.ConjLocal.conj_of_charpoly_local O n y'.val z'.val e12.symm (hsep _ e1)
    refine ⟨u, by rw [UL, if_pos hw]; exact Subgroup.mem_top _, ?_⟩
    rw [hu, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  · obtain ⟨-, hcc, hv, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩ := (h4 hw).2.1
    have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
    haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
    haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
      Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
    let c : O →+* O := (cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)
    have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hcc _)
    have hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι) := fun M => by
      ext i j; rfl
    have hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1 := fun x => by
      rw [UL, if_neg hw]
      change cT (cj w) x.val * 1 * x.val = 1 ↔ _
      rw [mul_one]
    have hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι := fun x => by
      ext i j; rfl
    have hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1 := fun x hx => by
      refine Matrix.map_injective hι ?_
      show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι
      rw [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]
      exact (hUL _).1 hx
    obtain ⟨u, hu, hcu⟩ := UnitInert.exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc
      (fun x hx => by
        rw [GlobalTheory.InertUQ.mem_max_iff] at hx ⊢
        exact (hv _).trans_lt hx)
      ⟨⟨x₀, hx₀⟩, by
        rw [← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]
        change ¬ Valued.v (x₀ - cj w x₀) < 1
        rw [Valuation.map_sub_swap, hx₁]
        exact lt_irrefl _⟩
      (hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1) e12
    refine ⟨u, ?_, hcu⟩
    rw [hUL]
    have := congrArg (fun M => M.map ι) hu
    simp only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this
    exact this

end GlobalTheory.BCT.IntUnitConj
end
end

