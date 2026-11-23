module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitaryAtAllRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarily
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
open Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Bridge Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteGroupUnitary

theorem isUnitaryRep_of_norm {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Representation ℂ G H) (h : ∀ g x, ‖ρ g x‖ = ‖x‖) : IsUnitaryRep ρ := by
  intro g x y
  let e : H →ₗᵢ[ℂ] H := ⟨ρ g, h g⟩
  exact e.inner_map_map x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

theorem pairAt_eq_of_rat (x y : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) : pairAt S σ x y = σ (S.pair x y) := by

  have hexp : S.pair x y = ∑ i, ∑ j, star (S.bV.repr x i) * S.gramV i j * S.bV.repr y j := by
    conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, CSD.gramV, Matrix.of_apply,
      starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairAt, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_

  have hc : ∀ τ : K →+* ℂ, τ (star (S.bV.repr x i)) = starRingEnd ℂ (τ (S.bV.repr x i)) := hx i
  rw [hc σ]

theorem csumAt_eq_of_rat (f f' : S.Cl → S.V) (hf : S.IsRat f) : csumAt S σ f f' = σ (S.csum f f') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [csumAt, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pairAt_eq_of_rat S σ (f c) (f' c) (fun i => hf c i)]

theorem csumAt_add_left (f g f' : S.Cl → S.V) : csumAt S σ (f + g) f' = csumAt S σ f f' + csumAt S σ g f' := by
  simp only [csumAt, pairAt, Pi.add_apply, map_add (f := _), Finsupp.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

theorem csumAt_smul_left (a : K) (f f' : S.Cl → S.V) :
    csumAt S σ (a • f) f' = starRingEnd ℂ (σ a) * csumAt S σ f f' := by
  simpa using csumAt_smul S σ a 1 f f'

private theorem csumAt_add_right (f g g' : S.Cl → S.V) :
    csumAt S σ f (g + g') = csumAt S σ f g + csumAt S σ f g' := by
  simp only [csumAt, pairAt, Pi.add_apply, map_add (f := _), Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

private theorem csumAt_smul_right' (b : K) (f f' : S.Cl → S.V) :
    csumAt S σ f (b • f') = σ b * csumAt S σ f f' := by
  simpa using csumAt_smul S σ 1 b f f'

private theorem csumAt_sum_left {ι : Type} (s : Finset ι) (F : ι → S.Cl → S.V) (f' : S.Cl → S.V) :
    csumAt S σ (∑ i ∈ s, F i) f' = ∑ i ∈ s, csumAt S σ (F i) f' := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [csumAt, pairAt]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, csumAt_add_left, ih]

private theorem csumAt_sum_right {ι : Type} (s : Finset ι) (f : S.Cl → S.V) (F : ι → S.Cl → S.V) :
    csumAt S σ f (∑ i ∈ s, F i) = ∑ i ∈ s, csumAt S σ f (F i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [csumAt, pairAt]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, csumAt_add_right, ih]

theorem csumAt_map (hb : S.HasRatBasis) (U : Module.End K S.Forms)
    (hU : ∀ f : S.Forms, S.IsRat (f : S.Cl → S.V) → S.IsRat (U f : S.Cl → S.V))
    (hc : ∀ f f' : S.Forms, S.csum (U f : S.Cl → S.V) (U f' : S.Cl → S.V) = S.csum (f : S.Cl → S.V) (f' : S.Cl → S.V))
    (f f' : S.Forms) :
    csumAt S σ (U f : S.Cl → S.V) (U f' : S.Cl → S.V) = csumAt S σ (f : S.Cl → S.V) (f' : S.Cl → S.V) := by
  obtain ⟨b, hbr⟩ := hb

  have key : ∀ i j, csumAt S σ (U (b i) : S.Cl → S.V) (U (b j) : S.Cl → S.V) =
      csumAt S σ (b i : S.Cl → S.V) (b j : S.Cl → S.V) := by
    intro i j
    rw [csumAt_eq_of_rat S σ _ _ (hU _ (hbr i)), csumAt_eq_of_rat S σ _ _ (hbr i), hc]

  rw [← b.sum_repr f, ← b.sum_repr f']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, csumAt_sum_left, csumAt_sum_right,
    csumAt_smul_left, csumAt_smul_right', key]

end ClassSum

section Presented

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}

theorem adInner_g0Act (l : LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι l.J y) (κ : l.Q) {F F' : G → W}
    (hF : F ∈ AdForms ι ρ l.J l.χ) (hF' : F' ∈ AdForms ι ρ l.J l.χ) :
    adInner ι l.J y (g0Act l.ch κ F) (g0Act l.ch κ F') = adInner ι l.J y F F' := by

  have hκ : ∀ k, (κ : G)⁻¹ * k * κ ∈ l.J ↔ k ∈ l.J := by
    intro k
    constructor
    · intro hk
      have h2 := hn (κ : G)⁻¹ (l.Q.inv_mem κ.2) _ hk
      have e : ((κ : G)⁻¹)⁻¹ * ((κ : G)⁻¹ * k * κ) * (κ : G)⁻¹ = k := by group
      rwa [e] at h2
    · intro hk
      exact hn κ κ.2 k hk
  have hχ : ∀ k : l.J, ‖(l.χ k : ℂ)‖ = 1 := fun k => by rw [← l.ch_J k]; exact hch _

  have hy' := GlobalTheory.ClassSumTranslate.isReps_mul ι hκ hy
  rw [← GlobalTheory.ClassSumTranslate.adInnerIndep ι ρ l.J l.χ hρ hχ I I (fun i => y i * κ) y hy' hy F hF F' hF']
  have hn1 : ‖(((l.ch κ)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hch κ, inv_one]
  have hc : starRingEnd ℂ (((l.ch κ)⁻¹ : ℂˣ) : ℂ) * (((l.ch κ)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [RCLike.conj_mul, hn1]
    simp
  unfold adInner g0Act
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.ClassSumTranslate.stab_mul ι hκ (y i), inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _), hc,
    one_mul]

theorem isUnitaryAtAll_of_tie (l : LevDatG G) (P : ClassPres ι S σ₀ ρ l.J l.χ) {G₀ : Type} [Group G₀]
    (act : Representation K G₀ S.Forms) (T : ActTie ι P l.Q l.ch act)
    (hσ : ∀ a : K, σ₀ (star a) = starRingEnd ℂ (σ₀ a))
    (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ∃ n : ℕ, 0 < n ∧ l.ch q ^ n = 1)
    (hrat : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ₀ (c i) • P.coef (S.bV i)) :
    IsUnitaryAtAll S act := by

  have hchn : ∀ q, ‖(l.ch q : ℂ)‖ = 1 := by
    intro q
    obtain ⟨n, hn, hq⟩ := hch q
    have h1 : (l.ch q : ℂ) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, hq, Units.val_one]
    have h2 : ‖(l.ch q : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2
  have hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ l.χ k ^ n = 1 := by
    intro k
    obtain ⟨n, hn, hk⟩ := hch ⟨k, l.J_le k.2⟩
    exact ⟨n, hn, by rw [← l.ch_J k]; exact hk⟩

  have hb : S.HasRatBasis := by
    refine (GlobalTheory.classPres_dcOp_rat ι S σ₀ ρ l.J l.χ P {1} 1 hσ hχ hrat ?_).1
    intro f
    funext h
    simp [dcOp]
  intro σ g f f'
  obtain ⟨κ, hκ⟩ := T.red_surj g
  refine csumAt_map S σ hb (act g) ?_ ?_ f f'
  ·

    intro f hf c i
    rw [← GlobalTheory.PresRat.mem_cmComplex_iff σ₀ hσ, ← GlobalTheory.PresBasic.repr_coef P, ← GlobalTheory.PresBasic.ext_y P, T.act_eq g κ hκ f]
    have hd := P.dec_spec (P.y c * (κ : G))
    unfold g0Act
    rw [hd, GlobalTheory.PresBasic.ext_dec P, map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine mul_mem ?_ (GlobalTheory.PresRat.act_mem P hσ hχ hrat _ _ _ (fun j => hf _ j) i)
    obtain ⟨n, hn, hq⟩ := hch κ
    refine GlobalTheory.PresRat.mem_cmComplex_of_pow hn ?_
    rw [← Units.val_pow_eq_pow_val, inv_pow, hq, inv_one, Units.val_one]
  ·
    intro f f'
    apply σ₀.injective
    have e1 := GlobalTheory.PresBasic.isom P (act g f) (act g f')
    have e2 := GlobalTheory.PresBasic.isom P f f'
    rw [← e1, ← e2, T.act_eq g κ hκ f, T.act_eq g κ hκ f']
    exact adInner_g0Act l hρ hn hchn P.reps κ (GlobalTheory.PresBasic.extMem P f) (GlobalTheory.PresBasic.extMem P f')

end Presented

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levEnv_ch_pow (V : TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : ∃ n : ℕ, 0 < n ∧ (levEnv V β L).ch q ^ n = 1 := by

  obtain ⟨n, hn, hx⟩ := isOfFinOrder_iff_pow_eq_one.1 (GlobalTheory.HeckeRational.levFn_isOfFinOrder β (Formalism.IndefR.Lev.flagL L)
    (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) q.1.1))
  refine ⟨n, hn, ?_⟩
  have e : (levEnv V β L).ch q = Formalism.L2.DIV.levFn β (Formalism.IndefR.Lev.flagL L)
      (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) q.1.1) := rfl
  rw [e, hx]

theorem definiteUnitary (R : RealDat D A Ks) (h : R.fam_tie) (hX : R.models_cX) (hV : R.models_cV) : DefiniteUnitary A := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  refine ⟨fun t => ?_, fun i t => ?_⟩
  ·
    exact isUnitaryAtAll_of_tie (levEnv D.sp.X' R.βX (R.datXt t)) (R.B.R t).pres (A.leftGroupActionRight t) (R.B.R t).act_tie
      D.starLL_cx (fun γ x x' => hX.2.1 _ x x') (GlobalTheory.ClassSumTranslate.levEnv_normal _ _ _) (levEnv_ch_pow _ _ _)
      (fun γ j => GlobalTheory.HeckeRational.action_rational _ _ (R.B.R t).pres (hT.coefR t) hT.mapR
        (fun g a b => (GlobalTheory.coefAction_repr_mem_subfield _ (cmMax D.what₂.LL) _
          (fun τ x => GlobalTheory.HeckeRational.labLL_mem_cmMax τ x) g a b).1) γ j)
  ·
    exact isUnitaryAtAll_of_tie (levEnv (Vc D i) (R.βV i) (R.datVt i t)) (R.B.L i t).pres (A.leftGroupActionLift i t) (R.B.L i t).act_tie
      D.starLL_cx (fun γ x x' => (hV i).2.1 _ x x') (GlobalTheory.ClassSumTranslate.levEnv_normal _ _ _) (levEnv_ch_pow _ _ _)
      (fun γ j => GlobalTheory.HeckeRational.action_rational _ _ (R.B.L i t).pres (hT.coefL i t) (hT.mapL i)
        (fun g a b => (GlobalTheory.coefAction_repr_mem_subfield _ (cmMax D.what₂.LL) _
          (fun τ x => GlobalTheory.HeckeRational.labLL_mem_cmMax τ x) g a b).2) γ j)

end GlobalTheory.FiniteGroupUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesClosed

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

def lowPart {m : ℕ} (M : Mx D m m) : Mx D m m := Matrix.of fun i j => if j ≤ i then M i j else 0

theorem continuous_lowPart {m : ℕ} : Continuous (lowPart (D := D) (m := m)) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Mx D m m => if j ≤ i then a i j else 0
    split_ifs
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const

theorem lowPart_eq_iff {m : ℕ} (M : Mx D m m) :
    lowPart M = lowPart 1 ↔ ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1 := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, ?_⟩
    · have := congrFun (congrFun h i) j
      simp only [lowPart, Matrix.of_apply, if_pos hji.le] at this
      rwa [Matrix.one_apply_ne hji.ne'] at this
    · have := congrFun (congrFun h i) i
      simp only [lowPart, Matrix.of_apply, if_pos (le_refl i), Matrix.one_apply_eq] at this
      exact this
  · intro h
    ext i j
    simp only [lowPart, Matrix.of_apply]
    split_ifs with hji
    · rcases hji.lt_or_eq with hlt | heq
      · rw [(h i j).1 hlt, Matrix.one_apply_ne hlt.ne']
      · subst heq; rw [(h j j).2, Matrix.one_apply_eq]
    · rfl

theorem strictUp_sub_one {m : ℕ} {M : Mx D m m} (h : ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1) :
    GlobalTheory.BesselChar.StrictUp (M - 1) := by
  intro j i hij
  rcases hij.lt_or_eq with hlt | heq
  · rw [Matrix.sub_apply, (h j i).1 hlt, Matrix.one_apply_ne hlt.ne', sub_zero]
  · subst heq; rw [Matrix.sub_apply, (h i i).2, Matrix.one_apply_eq, sub_self]

theorem mem_jacGrp_iff_mat (g : GA D S) : g ∈ jacGrp d ↔
    (d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧
      ∀ i j : Fin ρ, (j < i → (d.pX ⬝ (mt S g ⬝ d.jX)) i j = 0) ∧ (d.pX ⬝ (mt S g ⬝ d.jX)) i i = 1) := by
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    obtain ⟨u, hu, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
    have e : mt S (d.levi u * (d.nB b * d.nC c) * d.emb0 h) ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, GlobalTheory.MixPer.Decomp.mt_flag_jX]
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, d.pY_jX, d.pX_jX, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.one_mul]
    exact ⟨rfl, rfl, fun i j => hu i j⟩
  · rintro ⟨h0, hY, hX⟩
    obtain ⟨u, hu, hu1⟩ := GlobalTheory.MixPer.Decomp.exists_unit (strictUp_sub_one hX)
    have hu' : u.1 = d.pX ⬝ (mt S g ⬝ d.jX) := by rw [hu1, add_sub_cancel]
    have hgX : mt S g ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [hu']
      conv_lhs => rw [GlobalTheory.MixPer.Decomp.decomp d (mt S g ⬝ d.jX)]
      rw [h0, hY, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    have hst : (d.levi u)⁻¹ * g ∈ stabX d := mem_fixer.2 (GlobalTheory.MixPer.Decomp.fix_of_eq (by rw [d.levi_jX, hgX]))
    obtain ⟨n, hn, h, hnh⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.1 _).1 hst
    have hn' : n ∈ flagN d := (Subgroup.mem_inf.1 (show n ∈ flagN d ⊓ fixer S d.jX from hn)).1
    have e : g = d.levi u * n * d.emb0 h := by rw [mul_assoc, ← hnh, mul_inv_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem (d.levi_mem_NFlag hu) hn')) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem jacGrp_closed : IsClosed (jacGrp d : Set (GA D S)) := by
  haveI : T2Space (Mx D S₀.rank ρ) := (lattice_Mx D _ _).2.2.2.1
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D _ _).2.2.2.1
  have hc : Continuous fun g : GA D S => mt S g ⬝ d.jX := (continuous_mt S).matrix_mul continuous_const
  have e : (jacGrp d : Set (GA D S)) = {g | d.p0 ⬝ (mt S g ⬝ d.jX) = 0} ∩ {g | d.pY ⬝ (mt S g ⬝ d.jX) = 0} ∩
      {g | lowPart (d.pX ⬝ (mt S g ⬝ d.jX)) = lowPart 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_jacGrp_iff_mat, Set.mem_inter_iff, Set.mem_setOf_eq, lowPart_eq_iff, and_assoc]
  rw [e]
  exact ((isClosed_eq (continuous_const.matrix_mul hc) continuous_const).inter
    (isClosed_eq (continuous_const.matrix_mul hc) continuous_const)).inter
    (isClosed_eq (continuous_lowPart.comp (continuous_const.matrix_mul hc)) continuous_const)

theorem flagUnipotent_anisotropic_projection_eq_one {n : GA D S} (hn : n ∈ flagN d) : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]
  rw [d.nC_j0, d.nB_j0, ← Matrix.mul_assoc d.p0 (mt S (d.levi u)), d.wittDecomp_projAnisotropic_levi, Matrix.mul_add, d.p0_j0,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) = mt S₀ k := by
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n) d.j0, ← Matrix.mul_assoc d.p0, flagUnipotent_anisotropic_projection_eq_one d hn,
    Matrix.one_mul]


set_option maxHeartbeats 1000000 in
theorem exists_emb_of_fix {k : GA D S₀} (hk : mt S₀ k ⬝ o.jB = o.jB) : ∃ a : GA D A, o.emb (a, 1) = k := by
  have h1 : o.pB ⬝ (mt S₀ k ⬝ o.jA) = 0 := by
    have e : adj o.jB ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) = 0 := by
      conv_lhs => rw [← hk]
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
        ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_BA]
    rw [o.pB_eq, Matrix.mul_assoc, Matrix.mul_assoc, e, Matrix.mul_zero]
  obtain ⟨M, hM⟩ : ∃ M : Mx D A.rank A.rank, M = o.pA ⬝ (mt S₀ k ⬝ o.jA) := ⟨_, rfl⟩
  have hA : mt S₀ k ⬝ o.jA = o.jA ⬝ M := by
    calc mt S₀ k ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S₀ k ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ M := by rw [Matrix.add_mul, Matrix.mul_assoc o.jB, h1, Matrix.mul_zero, add_zero, Matrix.mul_assoc, hM]
  have hu : adj M * (gA A * M) = gA A := by
    calc adj M * (gA A * M) = adj (o.jA ⬝ M) ⬝ (gA S₀ ⬝ (o.jA ⬝ M)) := by
          rw [adj_mul, ← o.gram_AA]; simp only [Matrix.mul_assoc]
      _ = adj (mt S₀ k ⬝ o.jA) ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) := by rw [hA]
      _ = gA A := by
          rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
            ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_AA]
  have key : mt S₀ k = o.jA ⬝ M ⬝ o.pA + o.jB ⬝ o.pB := by
    have e : mt S₀ k ⬝ (o.jA ⬝ o.pA + o.jB ⬝ o.pB) = mt S₀ k := by rw [o.sum_eq_one]; exact Matrix.mul_one _
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hk] at e
    exact e.symm
  exact ⟨ofMat A M hu, mt_injective S₀ (by rw [o.mt_emb, mt_ofMat, mt_one, Matrix.mul_one, key])⟩

def prodSub : Subgroup (GA D S) where
  carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * embA d o h}
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, hn, h, rfl⟩ ⟨n', hn', h', rfl⟩
    refine ⟨n * (embA d o h * n' * (embA d o h)⁻¹), mul_mem hn ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 n' hn' _), h * h', ?_⟩
    rw [map_mul]; group
  inv_mem' := by
    rintro _ ⟨n, hn, h, rfl⟩
    refine ⟨embA d o h⁻¹ * n⁻¹ * (embA d o h⁻¹)⁻¹, (GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 _ (inv_mem hn) _, h⁻¹, ?_⟩
    rw [map_inv]; group

theorem besGrp_le_prodSub : besGrp d o ≤ prodSub d o :=
  sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, by simp⟩)

theorem besGrp_eq_inter :
    (besGrp d o : Set (GA D S)) = (jacGrp d : Set (GA D S)) ∩ {g | d.p0 ⬝ (mt S g ⬝ d.j0) ⬝ o.jB = o.jB} := by
  ext g
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := besGrp_le_prodSub d o hg
    refine ⟨mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨o.emb (h, 1), rfl⟩), ?_⟩
    show d.p0 ⬝ (mt S (n * d.emb0 (o.emb (h, 1))) ⬝ d.j0) ⬝ o.jB = o.jB
    rw [witt_anisotropic_block_flag_mul_embedded d hn, o.emb_jB, mt_one, Matrix.mul_one]
  · rintro ⟨hg, he⟩
    obtain ⟨n, hn, k, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    have he' : d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) ⬝ o.jB = o.jB := he
    rw [witt_anisotropic_block_flag_mul_embedded d hn] at he'
    obtain ⟨a, ha⟩ := exists_emb_of_fix o he'
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, by rw [embA_apply, ha]⟩)

theorem besGrp_isClosed : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L),
    IsClosed (besGrp d o : Set (GA D S)) := by
  intro D S S₀ A L ρ d o
  rw [besGrp_eq_inter]
  haveI : T2Space (Mx D S₀.rank L.rank) := (lattice_Mx D _ _).2.2.2.1
  exact (jacGrp_closed d).inter (isClosed_eq
    ((continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)).matrix_mul continuous_const)
    continuous_const)

end GlobalTheory.BesClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointSupportedOfConjHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSupp

theorem smul_mul_mul_of_smul_eq {R : Type} [CommRing R] {a b c d : Type} [Fintype b] [Fintype c]
    (r : R) (A : Matrix a b R) (N : Matrix b c R) (B : Matrix c d R) (h : r • N = N) :
    r • (A * N * B) = A * N * B := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem map_smul_of_smul_eq {R S : Type} [CommRing R] [CommRing S] {a b : Type} (f : R →+* S)
    (r : R) (N : Matrix a b R) (h : r • N = N) : f r • N.map f = N.map f := by
  ext k l
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [← map_mul]
  congr 1
  simpa [Matrix.smul_apply, smul_eq_mul] using congrFun (congrFun h k) l

theorem frMapAdj_supp : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T), e * e = e → IsHalf (cA D e) x → ∀ i j, toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  intro D S T βS βT e x he hx i j
  have hN : e • (x.map (cA D))ᵀ = (x.map (cA D))ᵀ := by
    ext k l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul]
    have h1 := hx l k
    have h2 : cA D (x l k) = e * cA D (x l k) := by
      conv_lhs => rw [← h1]
      rw [map_mul, cA_cA]
    exact h2.symm
  have hM := smul_mul_mul_of_smul_eq e ((S.gram⁻¹).map (incA D)) _ (T.gram.map (incA D)) hN
  have hM' := map_smul_of_smul_eq (toEAf D) e _ hM
  have hF := smul_mul_mul_of_smul_eq (toEAf D e) (βS⁻¹).val _ βT.val hM'
  have := congrFun (congrFun hF i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

end GlobalTheory.HalfSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupport
section
open GlobalTheory.Orb
open scoped Topology ContDiff Manifold

noncomputable section

namespace GlobalTheory

theorem glue_smooth_of_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c →
    HasCompactSupport f →
    (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧
      ∀ g, c g ∈ V → f g = Φ (c g)) →
    ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  intro H _ X _ _ _ c f hc hf hloc
  choose V hVo hcV Φ hΦ hfΦ using hloc
  have hs : IsClosed (c '' tsupport f) := (hf.isCompact.image hc).isClosed
  have hcov : c '' tsupport f ⊆ ⋃ a, V a := by
    rintro _ ⟨a, -, rfl⟩
    exact Set.mem_iUnion.2 ⟨a, hcV a⟩
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, X) hs V hVo hcov
  refine ⟨fun y => ∑ᶠ a, χ a y • Φ a y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    refine χ.contDiffAt_finsum fun a hy => ?_
    exact (hΦ a).contDiffAt ((hVo a).mem_nhds (hχ a hy))
  · intro g
    have hterm : ∀ a, χ a (c g) • Φ a (c g) = χ a (c g) • f g := by
      intro a
      by_cases h0 : χ a (c g) = 0
      · simp [h0]
      · have hmem : c g ∈ V a := hχ a (subset_tsupport _ h0)
        rw [hfΦ a g hmem]
    simp only [hterm]
    by_cases hg : g ∈ tsupport f
    · rw [← finsum_smul, χ.sum_eq_one ⟨g, hg, rfl⟩, one_smul]
    · have : f g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [this]

end GlobalTheory
end
end

