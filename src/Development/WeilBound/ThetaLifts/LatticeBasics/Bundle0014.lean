module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
public import Development.WeilBound.ThetaLifts.LatticeBasics.Unfold0
public import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.UnipUGood
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0014

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dens
open PositivityTheory.ThKF (ArchOp PureAct)
open PositivityTheory.ThK (LocRepEx)

def PolFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin a × Fin (a + a'))), FiniteDimensional ℂ U ∧
      ∀ k ∈ KInf σ G.W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U

namespace Prs

theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsOpen U ∧ IsCompact U}.Countable := by
  have hb := TopologicalSpace.isBasis_countableBasis X
  have hc := TopologicalSpace.countable_countableBasis X
  have hfin : {t : Set (Set X) | t.Finite ∧ t ⊆ TopologicalSpace.countableBasis X}.Countable :=
    Set.countable_setOf_finite_subset hc
  refine (hfin.image fun t => ⋃₀ t).mono ?_
  rintro U ⟨hU, hK⟩
  obtain ⟨S, hS, rfl⟩ := hb.open_eq_sUnion hU
  obtain ⟨t, htS, htf, hcov⟩ := hK.elim_finite_subcover_image (b := S) (c := fun s => s)
    (fun s hs => hb.isOpen (hS hs)) Set.sUnion_eq_biUnion.subset
  refine ⟨t, ⟨htf, htS.trans hS⟩, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.sUnion_subset_sUnion htS
  · simpa [Set.sUnion_eq_biUnion] using hcov

theorem mem_span_indicator {X : Type} [TopologicalSpace X] {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) :
    f ∈ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) := by
  classical
  obtain ⟨hl, hK⟩ := hf
  have hK' : IsCompact (tsupport f) := hK
  obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c})
    (fun c => hl.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hsum : f = ∑ c ∈ t, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage,
      Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      have hx : x ∈ tsupport f := subset_tsupport f (fun h0 => hne (by simpa using h0))
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hx)
      have : f x = c := hxc
      exact h (this ▸ hc)
  rw [hsum]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = 0
  · simp [hc]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨hl.isOpen_fiber c, ?_⟩, rfl⟩)
    refine hK'.of_isClosed_subset (hl.isClosed_fiber c) fun x hx => subset_tsupport f ?_
    have : f x = c := hx
    simpa [Function.mem_support, this] using hc

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  have hle : GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) :=
    fun f hf => mem_span_indicator hf
  refine (Submodule.rank_mono hle).trans ((rank_span_le _).trans ?_)
  exact Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen X).image _)

theorem rank_SB_Fv : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) (κ : Type) [Finite κ],
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)) ≤ Cardinal.aleph0 := by
  intro F _ _ v κ _
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := secondCountable_of_proper
  exact rank_SB_le _

theorem cartan_one {n r : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hs : HasSig M r 0) (h : IsCartan M θ) : θ = 1 := by
  obtain ⟨rfl, A, hA⟩ := hs
  let P : Matrix (Fin r) (Fin r) ℂ := A.submatrix id Sum.inl
  have e : Pᵀ * (M * P.map star) = 1 := by
    rw [← Matrix.mul_assoc]
    exact Matrix.ext fun i j => congrFun (congrFun hA (Sum.inl i)) (Sum.inl j)
  have e' : P * (M * P.map star)ᵀ = 1 := by
    rw [mul_eq_one_comm, ← transpose_transpose P, ← transpose_mul, transpose_transpose, e, transpose_one]
  have pos : ∀ x : Fin r → ℂ, 0 ≤ (x ⬝ᵥ M *ᵥ star x).re := fun x => by
    obtain ⟨y, rfl⟩ : ∃ y, x = P *ᵥ y := ⟨(M * P.map star)ᵀ *ᵥ x, by rw [mulVec_mulVec, e', one_mulVec]⟩
    have : star (P *ᵥ y) = P.map star *ᵥ star y := funext fun i => by simp [Matrix.mulVec, dotProduct]
    rw [this, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, e, one_mulVec]
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  refine Matrix.ext_iff_mulVec.2 fun u => ?_
  by_contra hu
  rw [one_mulVec] at hu
  have h1 := h.2.2 (θ *ᵥ u - u) (sub_ne_zero.2 hu)
  rw [mulVec_sub, mulVec_mulVec, h.1, one_mulVec, ← neg_sub, neg_dotProduct, Complex.neg_re] at h1
  linarith [pos (θ *ᵥ u - u)]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {R : RealMaps F a a'} {Rf : FinMaps F a a'} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
  {om' : Rep σ G.V' G.W}

theorem comm_theta (ht : IsTriple B G X om om') (hp : G.p = 0) (hq : G.q = 0) (w) (A) : Commute A (G.W.θ w) := by
  have h := ht.geo.hW.sig w
  rw [hp, hq] at h
  rw [cartan_one h (ht.geo.hW.cartan w)]
  exact Commute.one_right _

theorem deriv_mem {κ : Type} [Fintype κ] (U : Submodule ℂ (SInf F κ)) [FiniteDimensional ℂ U] (u : ℝ → SInf F κ)
    (hu : ∀ t, u t ∈ U) (f : SInf F κ) (h : ∀ x, HasDerivAt (fun t => u t x) (f x) 0) : f ∈ U := by
  let c : SInf F κ →ₗ[ℂ] (κ → mixedEmbedding.mixedSpace F) → ℂ := ⟨⟨fun g => g, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have h1 : Tendsto (fun t : ℝ => c (((t : ℂ)⁻¹) • (u t - u 0))) (𝓝[≠] 0) (𝓝 (c f)) := tendsto_pi_nhds.2 fun x => by
    refine (h x).tendsto_slope_zero.congr fun t => ?_
    show _ = (t : ℂ)⁻¹ * (u t x - u 0 x)
    rw [zero_add, Complex.real_smul, Complex.ofReal_inv]
  obtain ⟨g, hg, e⟩ := (U.map c).closed_of_finiteDimensional.mem_of_tendsto h1
    (Eventually.of_forall fun t => ⟨_, U.smul_mem _ (sub_mem (hu t) (hu 0)), rfl⟩)
  exact (DFunLike.coe_injective e : g = f) ▸ hg

theorem rank_pi (hm : IsMatched B G X om om' R Rf) (v : Pl F) : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
  rw [← rank_top, ← hm.fin.onto v]
  exact (rank_map_le _ _).trans (rank_SB_Fv _ _)

theorem irr_inf (hO : ArchOp) (hF : PolFin) (hm : IsMatched B G X om om' R Rf) (hp : G.p = 0) (hq : G.q = 0) (N : Submodule ℂ R.Pi)
    (h : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _,
      Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N) : N = ⊥ ∨ N = ⊤ := by
  refine hm.real.irred N (fun γ hγ f hf f₁ hd hN => ?_) h
  obtain ⟨U, hU, H⟩ := hF F E σ B a a' G X om om' hm.triple f hf
  have hk : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ KInf σ G.W B.emb := fun t => ⟨hγ.2 _, fun w => comm_theta hm.triple hp hq w _⟩
  choose A hA using fun t : ℝ => inf_op hO (PositivityTheory.ThKG.pairV hm.triple) (hk t)
  have hM := hm.triple.geo.hM
  have hr := Dat.rest (T := ∅) hM ⟨hf, fun v => (hM.vac v).1, fun _ _ => rfl⟩
  have : ∀ v, ∃ b, G.M.vac v b ≠ 0 ∧
      (G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, b i ∈ v.adicCompletionIntegers F) := fun v => by
    obtain ⟨b, hb⟩ := Function.ne_iff.1 (hM.vac v).2.1
    exact ⟨b, hb, fun e => by rw [e] at hb; exact Set.mem_of_indicator_ne_zero hb⟩
  choose b hb hb' using this
  let y : Fin a × Fin (a + a') → Af F := fun i => ⟨fun v => b v i, hM.std.mono fun v e => hb' v e i⟩
  have hc : (∏ᶠ v, G.M.vac v (b v)) ≠ 0 := finprod_induction (· ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hb
  haveI : FiniteDimensional ℂ ↥(U ⊓ N.comap R.p) := Submodule.finiteDimensional_inf_left _ _
  refine (deriv_mem (U ⊓ N.comap R.p) (fun t => A t f) (fun t => ⟨H _ (hk t) _ (hA t f hf).2,
    h _ (hk t) f hf _ (hA t f hf).2 hN⟩) f₁ fun x => ?_).2
  let z : Fin a × Fin (a + a') → AF F := fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i) : Ainf F × Af F)
  have e : ∀ g : SInf F (Fin a × Fin (a + a')), tens (evI F) g (finPart G.M.vac) z = g x * ∏ᶠ v, G.M.vac v (b v) := fun g =>
    congrArg (fun u => g u * _) (funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _)
  have := (hd _ hr z).div_const (∏ᶠ v, G.M.vac v (b v))
  simpa only [fun t => (hA t f hf).2 _ hr, e, mul_div_cancel_right₀ _ hc] using this

theorem fill (hL : LocRepEx) (hP : PureAct) (hO : ArchOp) (hF : PolFin) (hm : IsMatched B G X om om' R Rf) (hp : G.p = 0) (hq : G.q = 0) (T : Finset (Pl F))
    (N : Submodule ℂ (Fn F a (a + a'))) (hN : ∀ h, ∀ Φ ∈ N, om (1, h) Φ ∈ N) {Φ₀ ξ₀} (h0 : Φ₀ ∈ N)
    (c0 : (Φ₀, ξ₀) ∈ Cl B G.M R.p Rf.p T) (n0 : ξ₀ ≠ 0) (ξ) : ∃ Φ ∈ N, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T := by
  let S : Submodule ℂ (PiT R Rf T) := (Cl B G.M R.p Rf.p T ⊓ N.prod ⊤).map (LinearMap.snd _ _ _)
  have mS : ∀ η, η ∈ S ↔ ∃ Φ ∈ N, (Φ, η) ∈ Cl B G.M R.p Rf.p T := fun η =>
    ⟨by rintro ⟨z, ⟨h1, h2, -⟩, rfl⟩; exact ⟨z.1, h2, h1⟩, fun ⟨Φ, h1, h2⟩ => ⟨(Φ, η), ⟨h2, h1, trivial⟩, rfl⟩⟩
  obtain ⟨a₀, ha₀, hy⟩ := exists_tmul_mem (A := R.Pi) (X := fun v : T => Rf.Pi v)
    (fun v => {Op | ∃ h, ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ ∧ Op (Rf.p v φ) = Rf.p v φ₁})
    (fun v => rank_pi hm v) (fun v => hm.fin.nontriv v)
    (fun v P hs => hm.fin.irred v P fun h hh φ hφ φ₁ h₁ hact hφP => by
      obtain ⟨Op, o1, o2, -⟩ := fin_ops hL hm hh
      rw [← o2 φ hφ φ₁ h₁ hact]
      exact hs Op ⟨h, o1⟩ _ hφP) S
    (by
      rintro v Op ⟨h, o⟩ η hη
      obtain ⟨Φ, h1, h2⟩ := (mS η).1 hη
      exact (mS _).2 ⟨_, hN h Φ h1, cl_fin hP hm.triple.geo.hM v _ Op o h2⟩) ξ₀ ((mS _).2 ⟨_, h0, c0⟩) n0
  let Ni : Submodule ℂ R.Pi := ⨅ y, S.comap ((TensorProduct.mk ℂ R.Pi _).flip y)
  have mN : ∀ u, u ∈ Ni ↔ ∀ y, u ⊗ₜ[ℂ] y ∈ S := fun u => Submodule.mem_iInf _
  rcases irr_inf hO hF hm hp hq Ni (fun k hk f hf f₁ hact hmem => (mN _).2 fun y => by
    obtain ⟨Op, o1, o2, -⟩ := inf_ops hO hm hk
    obtain ⟨Φ, h1, h2⟩ := (mS _).1 ((mN _).1 hmem y)
    have := cl_inf hm.triple.geo.hM _ Op o1 h2
    rw [LinearMap.rTensor_tmul, o2 f hf f₁ hact] at this
    exact (mS _).2 ⟨_, hN k Φ h1, this⟩) with hb | ht
  · exact absurd ((Submodule.mem_bot ℂ).1 (hb ▸ (mN _).2 hy)) ha₀
  · refine (mS ξ).1 ?_
    induction ξ using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul u y => exact (mN u).1 (ht ▸ Submodule.mem_top) y

theorem pairs_lin (hm : IsMatched B G X om om' R Rf) {y y'} (h : y ∈ pairs B G X R Rf) (h' : y' ∈ pairs B G X R Rf) (c : ℂ) :
    y + c • y' ∈ pairs B G X R Rf :=
  ⟨add_mem h.1 (Submodule.smul_mem _ c h'.1), polMatch_add_smul hm h.2 h'.2 c⟩

end Prs

open Prs

theorem pairsStable_of (hS : PositivityTheory.ThKEnd.MatchStab) : PairsStable := fun F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hp hq =>
  ⟨fun _ h _ h' c => pairs_lin hm h h' c, fun y hy h =>
    hS F E σ B a a' G X om om' R Rf hm h (fun w => comm_theta hm.triple hp hq w _) y.1 y.2 hy.1 hy.2⟩

theorem pairsIrr_of (hL : LocRepEx) (hP : PureAct) (hO : ArchOp) (hF : PolFin) : PairsIrr := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hp hq N hsub hnull hst
  refine or_iff_not_imp_left.2 fun hn y hy => ?_
  push Not at hn
  obtain ⟨y₀, h0, n0⟩ := hn
  obtain ⟨T₀, hT₀, H₀⟩ := polMatch_big hm (hsub h0).2
  obtain ⟨T₁, -, H₁⟩ := polMatch_big hm hy.2
  have hT : X.T ⊆ T₀ ∪ T₁ := hT₀.trans Finset.subset_union_left
  obtain ⟨ξ₀, c0, -⟩ := H₀ _ (Finset.subset_union_left (s₂ := T₁))
  obtain ⟨ξ, c1, -⟩ := H₁ _ (Finset.subset_union_right (s₁ := T₀))
  obtain ⟨_, ⟨z, hz, rfl⟩, c2⟩ := fill hL hP hO hF hm hp hq _ (N.map (LinearMap.fst _ _ _))
    (by rintro h _ ⟨z, hz, rfl⟩; exact ⟨_, hst z hz h, rfl⟩) ⟨y₀, h0, rfl⟩ c0
    (fun e => n0 (polMatch_iff.2 ⟨_, hT, ξ₀, c0, e ▸ zero_mem _⟩)) ξ
  have h1 := hnull _ (pairs_lin hm hy (hsub hz) (-1))
    (polMatch_iff.2 ⟨_, hT, 0, by simpa [sub_eq_add_neg] using sub_mem c1 c2, zero_mem _⟩)
  simpa using N.add_mem h1 hz

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKEnd (unipU IsCusp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {χ : Chr F E} {z : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem absE_det' (d0 : Y.J.det ≠ 0) (h : UA σ Y.J) : absE F E (Matrix.GeneralLinearGroup.det h.1) = 1 := by
  have u : IsUnit (incM F Y.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact d0.isUnit.map _
  have e := congrArg Matrix.det (show (mat h)ᵀ * incM F Y.J * (mat h).map (cA σ) = incM F Y.J from h.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_right_comm, u.mul_eq_right,
    show ((mat h).map (cA σ)).det = sigR (AF F) σ (mat h).det from (RingHom.map_det (sigR (AF F) σ) _).symm] at e
  have e2 : Matrix.GeneralLinearGroup.det h.1 * GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det h.1) = 1 := Units.ext e
  have e3 := congrArg (absE F E) e2
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at e3
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, e3])

theorem Law.diag' (h : Law χ z f) (d0 : Y.J.det ≠ 0) (he : ∀ h h', IsEmb h h' (e (h, h'))) (g : UA σ Y.J) (x) :
    f (e (g, g) * x) * detInv χ g = f x := by
  rw [h _ _ x (he g g).par, absE_det' d0, detInv, mul_right_comm]; simp


variable (σ Y) in
abbrev Cos : Type := Quotient (QuotientGroup.rightRel ((par2 σ Y).subgroupOf (rat2 σ Y)))

theorem cos_eq {a b : rat2 σ Y} : (Quotient.mk _ a : Cos σ Y) = Quotient.mk _ b ↔ b.1 * a.1⁻¹ ∈ par2 σ Y :=
  Quotient.eq.trans (QuotientGroup.rightRel_apply.trans Subgroup.mem_subgroupOf)

theorem out_rel (γ : rat2 σ Y) : γ.1 * ((Quotient.mk _ γ : Cos σ Y).out.1)⁻¹ ∈ par2 σ Y :=
  cos_eq.1 (Quotient.mk _ γ : Cos σ Y).out_eq

theorem Law.out (h : Law χ z f) (hχ : IsHecke F E χ) (γ : rat2 σ Y) (x) : eisTerm f x (Quotient.mk _ γ) = f (γ.1 * x) :=
  (h.rat hχ (out_rel γ) (mul_mem γ.2 (inv_mem (Quotient.out _ : rat2 σ Y).2)) _).symm.trans (by simp [mul_assoc])

def rmul (c : rat2 σ Y) : Cos σ Y → Cos σ Y :=
  Quotient.map' (· * c) fun a b h => QuotientGroup.rightRel_apply.2 (by simpa using QuotientGroup.rightRel_apply.1 h)

theorem Law.rmul_eq (h : Law χ z f) (hχ : IsHecke F E χ) (c : rat2 σ Y) (q : Cos σ Y) (x) :
    eisTerm f x (rmul c q) = eisTerm f (c.1 * x) q := by
  induction q using Quotient.ind with
  | _ γ => exact (h.out hχ (γ * c) x).trans ((congrArg f (mul_assoc _ _ _)).trans (h.out hχ γ _).symm)

theorem Law.eis_rat (h : Law χ z f) (hχ : IsHecke F E χ) {Ê : G2 σ Y → ℂ} (hs : ∀ x, HasSum (eisTerm f x) (Ê x)) {c : G2 σ Y}
    (hc : c ∈ rat2 σ Y) (x) : Ê (c * x) = Ê x := by
  let u : Cos σ Y ≃ Cos σ Y := ⟨rmul ⟨c, hc⟩, rmul ⟨c, hc⟩⁻¹, fun q => by
    induction q using Quotient.ind with
    | _ γ => exact congrArg (Quotient.mk _) (mul_inv_cancel_right _ _), fun q => by
    induction q using Quotient.ind with
    | _ γ => exact congrArg (Quotient.mk _) (inv_mul_cancel_right _ _)⟩
  refine (hs _).unique ?_
  convert u.hasSum_iff.2 (hs x) using 1
  exact funext fun q => (h.rmul_eq hχ ⟨c, hc⟩ q x).symm

def ratE (he : ∀ h h', IsEmb h h' (e (h, h'))) (δ : ratU σ Y.J) : rat2 σ Y := ⟨e (1, δ), (he _ _).rat (one_mem _) δ.2⟩

@[reducible] def cosAct (he : ∀ h h', IsEmb h h' (e (h, h'))) : MulAction (ratU σ Y.J) (Cos σ Y) where
  smul δ := rmul (ratE he δ⁻¹)
  one_smul q := by
    induction q using Quotient.ind with
    | _ γ => exact congrArg (Quotient.mk _) (Subtype.ext (by simp [ratE, show ((1, 1) : UA σ Y.J × UA σ Y.J) = 1 from rfl]))
  mul_smul a b q := by
    induction q using Quotient.ind with
    | _ γ => exact congrArg (Quotient.mk _) (Subtype.ext (by simp [ratE, mul_assoc, ← map_mul]))

def Neg (e : UA σ Y.J × UA σ Y.J →* G2 σ Y) (q : Cos σ Y) : Prop := ¬ ∃ δ ∈ ratU σ Y.J, q.out.1 * (e (1, δ))⁻¹ ∈ par2 σ Y

theorem neg_iff (he : ∀ h h', IsEmb h h' (e (h, h'))) (q : Cos σ Y) : Neg e q ↔ ¬ ∃ δ, Quotient.mk _ (ratE he δ) = q :=
  not_congr ⟨fun ⟨δ, h1, h2⟩ => ⟨⟨δ, h1⟩, ((cos_eq (a := ratE he ⟨δ, h1⟩) (b := q.out)).2 h2).trans q.out_eq⟩,
    fun ⟨δ, h⟩ => ⟨δ, δ.2, (cos_eq (a := ratE he δ) (b := q.out)).1 (h.trans q.out_eq.symm)⟩⟩

theorem ratE_inj (he : ∀ h h', IsEmb h h' (e (h, h'))) : Function.Injective fun δ => (Quotient.mk _ (ratE he δ) : Cos σ Y) :=
  fun δ δ' h => by
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 ((cos_eq (a := ratE he δ) (b := ratE he δ')).1 h)
    change IsPar (e (1, δ') * (e (1, δ))⁻¹) t at ht
    rw [← map_inv, ← map_mul, isPar_iff, he] at ht
    simp only [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul] at ht
    obtain ⟨a, b⟩ := Matrix.fromRows_inj ht
    have : (1 : UA σ Y.J) * 1⁻¹ = δ'.1 * δ.1⁻¹ := Subtype.ext (Units.ext (a.trans b.symm))
    rw [inv_one, mul_one, eq_mul_inv_iff_mul_eq, one_mul] at this
    exact Subtype.ext this

theorem mem_stab (he : ∀ h h', IsEmb h h' (e (h, h'))) (q : Cos σ Y) (x : UA σ Y.J) :
    x ∈ (@MulAction.stabilizer _ _ _ (cosAct he) q).map (ratU σ Y.J).subtype ↔
      x ∈ ratU σ Y.J ∧ q.out.1 * e (1, x) * q.out.1⁻¹ ∈ par2 σ Y := by
  have k : ∀ δ : ratU σ Y.J, δ ∈ @MulAction.stabilizer _ _ _ (cosAct he) q ↔ q.out.1 * e (1, δ) * q.out.1⁻¹ ∈ par2 σ Y := fun δ => by
    change rmul (ratE he δ⁻¹) q = q ↔ _
    conv_lhs => rw [← q.out_eq]
    refine (cos_eq (a := q.out * ratE he δ⁻¹)).trans ?_
    change q.out.1 * (q.out.1 * e (1, δ.1⁻¹))⁻¹ ∈ par2 σ Y ↔ _
    rw [mul_inv_rev, ← map_inv, Prod.inv_mk, inv_one, inv_inv, mul_assoc]
  exact ⟨fun ⟨δ, h, e⟩ => e ▸ ⟨δ.2, (k δ).1 h⟩, fun h => ⟨⟨x, h.1⟩, (k _).2 h.2, rfl⟩⟩

open Classical in
theorem unfoldC (hO : OffOpen) (hU : PositivityTheory.ThKEnd.Grp.UnipUGood) {B : Base F E} {r s : ℕ} (hB : B.IsGood σ) (hY : Y.IsSkew σ B r s)
    (d0 : Y.J.det ≠ 0) [LocallyCompactSpace (UA σ Y.J)] [SecondCountableTopology (UA σ Y.J)] [T2Space (UA σ Y.J)]
    (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e) (cf : Continuous f) (hf : Law χ z f)
    {Ê : G2 σ Y → ℂ} (hs : ∀ x, HasSum (eisTerm f x) (Ê x)) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ Y.J) D μ) (hi : Integrable (fun g => f (e (1, g))) μ) {φ : UA σ Y.J → ℂ} (hφ : IsRapid φ)
    (hc : IsCusp Y φ) (h : UA σ Y.J) (hfin : ∑' q : Cos σ Y, ∫⁻ x in D, ‖eisTerm f (e (h, x)) q * detInv χ x * φ x‖ₑ ∂μ ≠ ⊤) :
    ∫ h' in D, Ê (e (h, h')) * detInv χ h' * φ h' ∂μ = ∫ g, f (e (1, g)) * detInv χ g * φ (h * g) ∂μ := by
  haveI := countable_ratU (σ := σ) (Y := Y)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : Countable (rat2 σ Y) := by
    haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
    haveI : Countable (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) := inferInstanceAs (Countable (_ → _ → E))
    haveI : Countable (GL (Fin n ⊕ Fin n) E) := Units.val_injective.countable
    exact (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)))).preimage
      Subtype.val_injective
  letI := cosAct he
  let T : Cos σ Y → UA σ Y.J → ℂ := fun q x => eisTerm f (e (h, x)) q * detInv χ x * φ x
  have cK : ∀ q, Continuous fun x => eisTerm f (e (h, x)) q * detInv χ x := fun q =>
    (cf.comp (continuous_const.mul (ce.comp (Continuous.prodMk_right h)))).mul (continuous_detInv hχ)
  have cT : ∀ q, Continuous (T q) := fun q => (cK q).mul hφ.1
  have sa : Summable fun q => ∫ x in D, T q x ∂μ := Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun q =>
    toReal_enorm (∫ x in D, T q x ∂μ) ▸ ENNReal.toReal_mono (ENNReal.ne_top_of_tsum_ne_top hfin q) (enorm_integral_le_lintegral_enorm _)
  have nd : ∀ (δ : ratU σ Y.J) q, Neg e (δ • q) ↔ Neg e q := fun δ q => by
    rw [neg_iff he, neg_iff he]
    have k : ∀ (δ η : ratU σ Y.J), δ • (Quotient.mk _ (ratE he η) : Cos σ Y) = Quotient.mk _ (ratE he (η * δ⁻¹)) := fun δ η =>
      congrArg (Quotient.mk _) (Subtype.ext (by simp [ratE, ← map_mul]))
    exact not_congr ⟨fun ⟨η, hη⟩ => ⟨η * δ⁻¹⁻¹, by rw [← k, hη, inv_smul_smul]⟩, fun ⟨η, hη⟩ => ⟨η * δ⁻¹, by rw [← k, hη]⟩⟩
  have neg : ∑' q, ∫ x in D, (if Neg e q then T q x else 0) ∂μ = 0 := by
    refine GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero _ μ (ratU σ Y.J) (Cos σ Y) D hD (fun q x => if Neg e q then T q x else 0)
      (fun q => by split_ifs; exacts [(cT q).measurable, measurable_const]) (fun δ q x => ?_)
      (ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun q => lintegral_mono fun x => by split_ifs; exacts [le_rfl, by simp]))
      fun q 𝓖 h𝓖 ig => ?_
    · rw [nd]
      refine if_congr Iff.rfl ?_ rfl
      change eisTerm f _ (rmul _ q) * _ * _ = _
      rw [hf.rmul_eq hχ, detInv_mul, detInv_rat hχ δ.2, one_mul, hφ.2.1 _ δ.2]
      simp [T, ratE, ← map_mul]
    by_cases hq : Neg e q
    swap
    · simp [hq]
    simp only [if_pos hq] at ig ⊢
    obtain ⟨U, u1, u2, u3, u4⟩ := hO F E σ B n Y r s hB hY e he _ q.out.2 hq
    obtain ⟨g, -⟩ := hU F E σ hB.cm n Y (.inr hY.skew) d0 U
    obtain ⟨κ, 𝓜, k1, k2, k3⟩ := g.ex
    have st := mem_stab he q
    have mv : ∀ δ x, q.out.1 * e (h, δ * x) = q.out.1 * e (1, δ) * q.out.1⁻¹ * (q.out.1 * e (h, x)) := fun δ x => by
      simp [mul_assoc, ← map_mul]
    refine GlobalTheory.UnfoldNormal.unfold_zero_mean _ μ _ (unipU σ Y U) (Set.Countable.mono (fun x hx => ((st x).1 hx).1)
      (Set.countable_coe_iff.1 countable_ratU)).to_subtype g.closed (fun δ hδ => u4 δ ((st δ).1 hδ).1 ((st δ).1 hδ).2) κ 𝓜 k1 ?_
      (by simp [k3]) _ φ (cK q).measurable hφ.1.measurable (fun m hm x => ?_) (fun δ hδ x => ?_)
      (fun δ hδ => hφ.2.1 δ ((st δ).1 hδ).1) (hc U u1 u2 κ 𝓜 k1 k2) 𝓖 h𝓖 ig
    · refine (Subgroup.ext fun m => ?_ : (ratU σ Y.J).subgroupOf (unipU σ Y U) =
        ((MulAction.stabilizer (ratU σ Y.J) q).map (ratU σ Y.J).subtype).subgroupOf (unipU σ Y U)) ▸ k2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, st]
      exact ⟨fun h => ⟨h, mem_parabolic_GL2_iff.2 ((u3 m m.2).imp fun _ => And.left)⟩, And.left⟩
    · obtain ⟨t, t1, t2, t3⟩ := u3 m hm
      simp only [eisTerm]
      rw [mv, hf _ t _ t1, t2, detInv_mul, detInv, t3]; simp
    · simp only [eisTerm]
      rw [mv, hf.rat hχ ((st δ).1 hδ).2 (mul_mem (mul_mem q.out.2 ((he _ _).rat (one_mem _) ((st δ).1 hδ).1)) (inv_mem q.out.2)),
        detInv_mul, detInv_rat hχ ((st δ).1 hδ).1, one_mul]
  obtain ⟨C, hC⟩ := hφ.2.2 0
  let k : UA σ Y.J → ℂ := fun g => f (e (1, g)) * detInv χ g * φ (h * g)
  have ik : Integrable k μ := by
    simp only [k, mul_assoc]
    exact hi.mul_bdd (c := C) ((continuous_detInv hχ).mul (hφ.1.comp (continuous_const_mul h))).aestronglyMeasurable
      (.of_forall fun g => by simpa [norm_detInv] using hC (h * g))
  have op : ∀ δ : ratU σ Y.J, ∀ x, T (Quotient.mk _ (ratE he δ)) x = k (h⁻¹ * (δ • x)) := fun δ x => by
    simp only [k, T, hf.out hχ, ratE, Subgroup.smul_def, smul_eq_mul]
    rw [← Law.diag' hf d0 he h (e (1, h⁻¹ * _)), ← map_mul, ← map_mul, detInv_mul, detInv_mul, detInv_rat hχ δ.2, mul_inv_cancel_left,
      hφ.2.1 _ δ.2]
    have : detInv χ h * detInv χ h⁻¹ = 1 := by rw [← detInv_mul, mul_inv_cancel, detInv_rat hχ (one_mem _)]
    simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_inv_cancel_left]
    linear_combination (-(f (e (h, δ * x)) * detInv χ x * φ x)) * this
  have sb : ∀ (p : Cos σ Y → Prop) [DecidablePred p], Summable fun q => if p q then ∫ x in D, T q x ∂μ else 0 := fun p _ =>
    Summable.of_norm_bounded sa.norm fun q => by split_ifs; exacts [le_rfl, by simp]
  calc _ = ∫ x in D, ∑' q, T q x ∂μ := integral_congr_ae (.of_forall fun x => (((hs _).mul_right _).mul_right _).tsum_eq.symm)
    _ = ∑' q, ∫ x in D, T q x ∂μ := integral_tsum (fun q => (cT q).aestronglyMeasurable) hfin
    _ = ∑' q, ((if Neg e q then ∫ x in D, T q x ∂μ else 0) + if ¬ Neg e q then ∫ x in D, T q x ∂μ else 0) :=
        tsum_congr fun q => by by_cases hq : Neg e q <;> simp [hq]
    _ = ∑' q, if ¬ Neg e q then ∫ x in D, T q x ∂μ else 0 := by
        rw [(sb (Neg e)).tsum_add (sb fun q => ¬ Neg e q), add_eq_right]
        refine Eq.trans ?_ neg
        exact tsum_congr fun q => by by_cases hq : Neg e q <;> simp [hq]
    _ = ∑' δ : ratU σ Y.J, ∫ x in D, k (h⁻¹ * (δ • x)) ∂μ := by
        rw [← (ratE_inj he).tsum_eq]
        · exact tsum_congr fun δ => by rw [if_pos (by rw [neg_iff he, not_not]; exact ⟨δ, rfl⟩)]; simp only [op]
        · intro q hq
          by_contra hn
          exact hq (if_neg (not_not.2 ((neg_iff he q).2 hn)))
    _ = _ := by
        rw [← hD.integral_eq_tsum'' (fun x => k (h⁻¹ * x)) (ik.comp_mul_left h⁻¹), integral_mul_left_eq_self k]

end GlobalTheory.ThK.Dbl

end
end

