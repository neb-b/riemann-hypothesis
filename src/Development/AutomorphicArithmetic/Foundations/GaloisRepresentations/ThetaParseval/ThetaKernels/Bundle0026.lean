module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtExA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0019
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0020
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefBd
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0002
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtExA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Hgt
open scoped Matrix TensorProduct NNReal
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl GlobalTheory.WeilM
open GlobalTheory.CompanionTheory.IwaDbl.FrameCore
open Formalism.UG (cT bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem exists_scal_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) :
    ∃ ξ : E, ξ ≠ 0 ∧ (∀ i j, σ ((ξ • Y.Jᵀ) j i) = (ξ • Y.Jᵀ) i j) ∧ ∀ w, ∃ (M : Matrix (Fin n) (Fin n) ℂ) (r : ℝ), Mᴴ = M ∧
      IsCartan M (Y.θ w) ∧ r ≠ 0 ∧ (ξ • Y.Jᵀ).map (B.emb w).1 = (r : ℂ) • Mᵀ := by
  have hc := hB.cm
  rcases hY with h | h
  · refine ⟨1, one_ne_zero, fun i j => by simpa using h.herm j i, fun w => ⟨_, 1, ?_, h.cartan w, one_ne_zero, ?_⟩⟩
    · exact Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))
    · ext i j; simp
  · obtain ⟨x, hx⟩ : ∃ x, x - σ x ≠ 0 := by
      by_contra! e
      have := hc.2.1
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
        (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
          (hc.2.2.2 τ y).symm.trans (congrArg τ (sub_eq_zero.1 (e y)).symm))))
    have hs : σ (x - σ x) = -(x - σ x) := by rw [map_sub, cm_conj_conj hc, neg_sub]
    refine ⟨_, hx, fun i j => ?_, fun w => ?_⟩
    · change σ (_ * Y.J i j) = _ * Y.J j i
      rw [map_mul, hs, h.skew, neg_mul_neg]
    · have h1 := hc.2.2.2 (B.emb w).1 (x - σ x)
      rw [hs, map_neg] at h1
      have h2 : (B.emb w).1 (x - σ x) = ((B.emb w).1 (x - σ x)).im * Complex.I := by
        have := congrArg Complex.re h1
        simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
        exact Complex.ext (by simp only [Complex.mul_I_re, Complex.ofReal_im]; linarith) (by simp)
      refine ⟨_, ((B.emb w).1 (x - σ x)).im, Matrix.ext fun i j => ?_, h.cartan w, fun e => hx ?_, Matrix.ext fun i j => ?_⟩
      · change star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)
        rw [star_mul', ← hc.2.2.2, h.skew]; simp
      · rw [e] at h2
        exact (map_eq_zero _).1 (h2.trans (by simp))
      · change (B.emb w).1 (_ * Y.J j i) = _ * (Complex.I * (B.emb w).1 (Y.J j i))
        rw [map_mul, ← mul_assoc, ← h2]
theorem iwasawa2_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (x : G2 σ Y) :
    ∃ p : siegelOf (Equiv.refl (Fin n ⊕ Fin n)) (UG (cA σ) (dbl (incM F Y.J))).subtype, ∃ k ∈ stab2 σ Y B, x = p * k := by
  have hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨ξ, hξ, hh, hw⟩ := _root_.GlobalTheory.ThK.Dbl.Hgt.exists_scal_k hB hY
  choose M r h1 h2 h3 h4 using hw
  choose b hb hb' using fun w => exists_arch hB.cm (B.emb w) (h1 w) (isUnit_of_cartan (h2 w)) (h2 w) (h3 w) (h4 w)
  obtain ⟨a, -, ha⟩ := Frames.exists_isLatticeFrame_of_arch Y.L b
  obtain rfl : b = fun w => bc (compInf F E w) a := (funext ha).symm
  obtain ⟨g, rfl⟩ := back_surj hξ x
  obtain ⟨p, k, hk, rfl⟩ := HasIwasawa.adelic (a := a) (_root_.GlobalTheory.ThK.Dbl.Hgt.hasIwasawa_fin'_k hB hY (det_ne hY) hξ hh) hb g
  have k2 := keeps_back hL.fg hξ (mem_KAd.1 (inv_mem hk)).1
  rw [map_inv] at k2
  exact ⟨⟨_, back_mem_par hξ p.2⟩, back σ Y hξ k, ⟨fun w => back_comm hξ _ ((hb' w _).1 ((mem_KAd.1 hk).2 w)),
    keeps_back hL.fg hξ (mem_KAd.1 hk).1, k2⟩, map_mul _ _ _⟩
theorem hgtEx_core_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hK : IsCompact (stab2 σ Y B : Set (G2 σ Y))) :
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h')) := by
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hI := iwasawaOf_of_isCompact (ν := absE F E) continuous_subtype_val continuous_absE hK (_root_.GlobalTheory.ThK.Dbl.Hgt.iwasawa2_k hB hY)
  refine ⟨⟨_, fun x => hgtOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype (absE F E) (stab2 σ Y B) x, isStab2_stab2 B,
    ⟨fun x => ?_, fun p t hp k hk => ?_⟩,
    NNReal.continuous_coe.comp (hI.continuous_hgtOf continuous_subtype_val continuous_absE hK), fun x => hgtOf_pos x⟩,
    emb2 σ Y, ((continuous_blkGL _).comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _, fun _ _ => rfl⟩
  · obtain ⟨p, h⟩ := _root_.GlobalTheory.ThK.Dbl.Hgt.iwasawa2_k hB hY x
    exact ⟨p, leviOf _ _ p, isPar_iff.2 ⟨mem_siegelOf.1 p.2, rfl⟩, h⟩
  · obtain ⟨h1, h2⟩ := isPar_iff.1 hp
    have := hI.hgtOf_mul ⟨p, mem_siegelOf.2 h1⟩ hk
    rw [show t = leviOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype ⟨p, mem_siegelOf.2 h1⟩ from Units.ext h2.symm]
    exact congrArg NNReal.toReal this
end GlobalTheory.ThK.Dbl.Hgt
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseKPair
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
def Stab2Cpt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → IsCompact (K : Set (G2 σ Y))
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} {χ : Chr F E} {z s₀ : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}
theorem kpair_cont_k {B : Base F E} {r s : ℕ} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (h0 : min r s = 0)
    (c : Cpt σ Y.J) (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e)
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) (ca : Continuous a) (a0 : ∀ x, 0 < a x) (cf : Continuous f) (hf : Law χ z f)
    {U Ê} (hE : IsEisCont (flat a f s₀) U Ê) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ Y.J) D μ) {t₀ : ℝ} (hi : ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ) :
    (∀ φ, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U) ∧ ∃ t : ℝ, ∀ s : ℂ, t < s.re → s ∈ U ∧
      Integrable (fun g => flat a f s₀ s (e (1, g)) * detInv χ g) μ ∧ ∀ φ, IsRapid φ → kpair χ e μ D (Ê s) φ =
        ∫ g, flat a f s₀ s (e (1, g)) * detInv χ g * pet μ D (fun h => φ (h * g)) φ ∂μ := by
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hB hY h0
  obtain ⟨t₁, half⟩ := hE.half
  haveI := c.sc; haveI := c.lc
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using c.fin _ _ hμ hD⟩
  have bc : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → An.BC φ := fun h => ⟨h.1, c.bdd h.1 h.2.1⟩
  have cE : ∀ s ∈ U, Continuous (Ê s) := fun s hs =>
    hE.cont.comp_continuous (f := fun x => (s, x)) (by fun_prop) fun _ => ⟨hs, trivial⟩
  have iv : ∀ s ∈ U, ∀ γ ∈ ratU σ Y.J, ∀ δ ∈ ratU σ Y.J, ∀ g g', Ê s (e (γ * g, δ * g')) = Ê s (e (g, g')) := fun s hs γ hγ δ hδ g g' =>
    An.ident hE.isOpen hE.conn (hE.hol _) (hE.hol _) (fun s hs => ⟨(half s hs).1, by
      rw [← Prod.mk_mul_mk, map_mul]; exact (hf.flat ha a0 s).eis_inv hχ hJ he (half s hs).2 hγ hδ _⟩) hs
  have ck : ∀ s ∈ U, An.BC fun y : UA σ Y.J × UA σ Y.J => Ê s (e y) * detInv χ y.2 := fun s hs =>
    An.BC.mul ⟨(cE s hs).comp ce, c.bdd₂ c ((cE s hs).comp ce) (iv s hs)⟩
      ⟨(continuous_detInv hχ).comp continuous_snd, 1, fun y => (norm_detInv _ _).le⟩
  have hol : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U := fun {φ} h => by
    have b := ((bc h).comp (continuous_snd (X := UA σ Y.J))).mul ((bc h).comp continuous_fst).star
    refine An.diffOn_integral hE.isOpen (fun s hs => ((ck s hs).mul b).1.aestronglyMeasurable)
      (fun y => ((hE.hol _).mul_const _).mul_const _) fun S hS cS => ?_
    obtain ⟨Ω, hΩ, cov⟩ := c.cov
    obtain ⟨C, hC⟩ := (cS.prod ((hΩ.prod hΩ).image ce)).exists_bound_of_continuousOn
      (hE.cont.mono (Set.prod_mono hS (Set.subset_univ _)))
    obtain ⟨C', hC'⟩ := b.2
    refine ⟨C * C', fun s hs y => ?_⟩
    obtain ⟨γ, hγ, h1⟩ := cov y.1
    obtain ⟨δ, hδ, h2⟩ := cov y.2
    have := hC (s, e (γ * y.1, δ * y.2)) ⟨hs, _, ⟨h1, h2⟩, rfl⟩
    rw [iv s (hS hs) γ hγ δ hδ] at this
    rw [norm_mul, norm_mul, norm_detInv, mul_one]
    exact mul_le_mul this (hC' y) (norm_nonneg _) ((norm_nonneg _).trans this)
  refine ⟨fun _ => hol, max t₁ (t₀ + s₀.re - z.re), fun s hs => ?_⟩
  obtain ⟨u, sm⟩ := half s ((le_max_left _ _).trans_lt hs)
  have cs := continuous_flat (s₀ := s₀) cf ca a0 s
  obtain ⟨C, hC⟩ := (hf.flat (s₀ := s₀) ha a0 s).bound cs ha hK
  have i1 : Integrable (fun g => flat a f s₀ s (e (1, g))) μ :=
    ((hi (s - s₀ + z).re (by have := (le_max_right _ _).trans_lt hs; simp; linarith)).const_mul C).mono'
      (cs.comp (ce.comp (Continuous.prodMk_right 1))).aestronglyMeasurable (.of_forall fun g => hC _)
  have i2 := i1.mul_bdd (continuous_detInv hχ).aestronglyMeasurable (.of_forall fun g => (norm_detInv χ g).le)
  exact ⟨u, i2, fun φ h => An.far_right _ μ (ck s u) (bc h) i2
    (_root_.GlobalTheory.ThK.Dbl.unfold0_k F E σ B n Y r _ hB hY h0 χ e hχ he _ _ _ cs (cE s u) sm (hf.flat ha a0 s) μ D hμ hD i1 _ h)⟩
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseNormZeta
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
theorem swFullX_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.SWAnisoX_k) (h2 : _root_.GlobalTheory.ThK.Dbl.EisContinues_k) (h3 : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k) : _root_.GlobalTheory.ThK.Dbl.SWFullX_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n X r s hB hn (.inl hX) χ hχ d hr K a hK ha _ _
    (h3 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((d : ℂ) - n) / 2)
  exact ⟨_, _, hE.update hk (h1 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBasePairsL
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Prs
open scoped TensorProduct Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dens
open PositivityTheory.ThKF (ArchOp PureAct)
open PositivityTheory.ThK (LocRepEx)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ Y W} {o : Rep σ Y W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
  {p : SInf F (Fin n × Fin d) →ₗ[ℂ] R.Pi} {q : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Rf.Pi v} {T T₁ : Finset (Pl F)}
theorem inf_op_k (hA : _root_.PositivityTheory.ThKF.ArchOp_k) {χ χ' r s r' s'} (hp : _root_.GlobalTheory.ThK.IsPair_k B M χ χ' o r s r' s') {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ A : Module.End ℂ (SInf F (Fin n × Fin d)), ∀ f ∈ M.Pol B.ψ B.emb, A f ∈ M.Pol B.ψ B.emb ∧ Acts (evI F) (o (1, k)) f (A f) := by
  have o1 : (1 : UA σ Y.J) ∈ KInf σ Y B.emb :=
    ⟨fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero], fun w => by
      rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩
  obtain ⟨A, a1, a2⟩ := hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp 1 o1.1 k hk.1
  exact ⟨A, fun f hf => ⟨a2 o1 hk f hf, a1.2 f⟩⟩
variable {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
end GlobalTheory.ThK.Dbl.Prs
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStdEx
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
def StdEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∃ b K a, IsFrame2 σ Y b ∧ IsStdK (σ := σ) (Y := Y) B b K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x
theorem stdEx_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) (h2 : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) : _root_.GlobalTheory.ThK.Dbl.StdEx_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY
  obtain ⟨⟨K, a, hK, ha, hc, hp⟩, -⟩ := h2 F E σ B n Y r s hB hY
  obtain ⟨b, K₀, p, t, hb, hK₀, hpt, e⟩ := h1 F E σ B n Y r s hB hY K hK
  have h0 : (0 : ℝ) < absE F E (Matrix.GeneralLinearGroup.det t) := by
    rw [← ha.val p t hpt 1 K.one_mem]
    exact hp _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  refine ⟨b, K₀, fun x => absE F E (Matrix.GeneralLinearGroup.det t) * a (x * p⁻¹), hb, hK₀, ⟨fun x => ?_, fun q u hq k hk => ?_⟩,
    continuous_const.mul (hc.comp (continuous_mul_const _)), fun x => mul_pos h0 (hp _)⟩
  · obtain ⟨q, u, hq, k, hk, ex⟩ := ha.iwa (x * p⁻¹)
    exact ⟨q * p, u * t, hq.mul hpt, _, (e k).1 hk, by rw [mul_inv_eq_iff_eq_mul.1 ex]; group⟩
  · have := ha.val _ _ (hq.mul hpt.inv) (p * k * p⁻¹) ((e _).2 (by convert hk using 1; group))
    rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, this, ← NNReal.coe_mul, ← map_mul, mul_comm, ← map_mul,
      inv_mul_cancel_right]
end GlobalTheory.ThK.Dbl
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstCoefBd
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK NumberField.mixedEmbedding
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open scoped TensorProduct ENNReal NNReal Classical
noncomputable section
namespace PositivityTheory.ThKEst
namespace W
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
end W
open W
theorem coefBd_of_k : CoefReal → _root_.PositivityTheory.ThKEst.CoefBd_k := by
  intro hR F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ φ₁ h₁ φ₂ h₂ N
  haveI := hP.base.cm.1
  obtain ⟨p, C, K, hp, hC, hK, h⟩ := coef_split hR hP.base.std μ hμ h₁ h₂ N
  obtain ⟨L, hL, hsz⟩ := sz_le B.emb M.co.e.symm.toLinearMap
  have hLN : 0 ≤ C * L ^ N := by positivity
  refine ⟨(NNReal.mk (1 + C * L ^ N) (by positivity)) • p,
    (fun q => M.co.e.symm (spl F _ (0, q.1), spl F _ (0, q.2))) '' K, hp.const_smul _,
    hK.image ((lin_cont M.co.e.symm.toLinearMap).comp ((spl_cont.comp (continuous_const.prodMk continuous_fst)).prodMk
      (spl_cont.comp (continuous_const.prodMk continuous_snd)))), fun f₁ f₂ z => ?_⟩
  obtain ⟨w, rfl⟩ := M.co.e.symm.surjective z
  obtain ⟨x, hx⟩ := (spl F _).surjective w.1
  obtain ⟨y, hy⟩ := (spl F _).surjective w.2
  obtain rfl : w = (spl F _ x, spl F _ y) := Prod.ext hx.symm hy.symm
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨a, b⟩ := h f₁ f₂ x y
  by_cases h0 : coef F B.ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (spl F _ x, spl F _ y) = 0
  · rw [h0, norm_zero]
    exact mul_nonneg (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (LatticeQuotientCompactness.maj_nonneg _ _ _ _)
  have s0 := LatticeQuotientCompactness.sz_nonneg B.emb (M.co.e.symm (spl F _ x, spl F _ y))
  rw [maj, if_pos, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  · have q := mul_nonneg (apply_nonneg p f₁) (apply_nonneg p f₂)
    calc _ ≤ _ * (L * (1 + ‖x.1‖ + ‖y.1‖)) ^ N := by gcongr; exact hsz x y
      _ = L ^ N * (_ * (1 + ‖x.1‖ + ‖y.1‖) ^ N) := by rw [mul_pow, mul_left_comm]
      _ ≤ L ^ N * (C * (p f₁ * p f₂)) := by gcongr
      _ ≤ ((1 + C * L ^ N) * p f₁) * ((1 + C * L ^ N) * p f₂) := by
        nlinarith [mul_nonneg hLN q, mul_nonneg (mul_nonneg hLN hLN) q]
  · refine ⟨_, ⟨_, b h0, rfl⟩, fun u hu => ?_⟩
    rw [← map_sub, ← map_smul, map_eq_zero_iff _ M.co.e.symm.injective, Prod.mk_sub_mk, ← map_sub, ← map_sub]
    have : ∀ x : (Fin n × Fin d → mixedSpace F) × (Fin n × Fin d → Af F), u • spl F _ (x - (0, x.2)) = 0 := fun x =>
      funext fun i => by
        show u * (re F _ + fi F (x.2 i - x.2 i)) = 0
        rw [sub_self, map_zero, add_zero, ← re_add_fi u, hu, map_zero, zero_add, mul_comm, re_mul_fi]
    exact Prod.ext (this x) (this y)
end PositivityTheory.ThKEst
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstCoefEq
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
theorem coefEq_of_k : _root_.PositivityTheory.ThKEst.CoefEq_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ Φ₁ h₁ Φ₂ h₂ g h z
  have hs := IsUWeilPair.isUSplitting hP.weil
  set w := mat g⁻¹ * z * (mat h⁻¹)ᵀ with hw
  have e : actAB (cA σ) (g, h) w = z := by
    have a : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1
    have b : (mat h⁻¹)ᵀ * (mat h)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show mat h * mat h⁻¹ = 1 from Units.mul_inv h.1, Matrix.transpose_one]
    change mat g * w * (mat h)ᵀ = z
    rw [hw, Matrix.mul_assoc (mat g⁻¹), ← Matrix.mul_assoc (mat g), a, Matrix.one_mul, Matrix.mul_assoc, b,
      Matrix.mul_one]
  have i := hs.impl (g, h) w Φ₁ h₁
  rw [e] at i
  have k := inner_eq_of_unit μ (om (g, h)) (hs.pres _) (hs.unit μ hμ _)
    (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std w Φ₁ h₁) h₂
  rw [i] at k
  exact k
end PositivityTheory.ThKEst
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstEpsOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
namespace SignatureOfHermitianForm
end SignatureOfHermitianForm
theorem epsOf_of_k : _root_.PositivityTheory.ThKEst.EpsOf_k := by
  intro F E _ _ _ _ _ σ B hB n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hτ := hB.cm.2.2.2 (B.emb w).1
  rcases hX with hX | hX
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J 1 one_ne_zero (r := r) (s := s) (by rw [one_smul]; exact hX.sig w)
    exact ⟨⟨Or.inl hX.herm, this.1⟩, this.2⟩
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J Complex.I Complex.I_ne_zero (hX.sig w)
    exact ⟨⟨Or.inr hX.skew, this.1⟩, this.2⟩
end PositivityTheory.ThKEst
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstLevel
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
namespace levelStructure
open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
end levelStructure
open levelStructure in
theorem level_of_k (hC : _root_.PositivityTheory.ThKEst.CoefEq_k) (hF : FourierInj) (hB : _root_.PositivityTheory.ThKEst.CoefBd_k) : _root_.PositivityTheory.ThKEst.Level_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := coef_near M hp.base.std hφ hCc
  have := LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ W.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin d) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ W.J => ‖om (1, u) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_const.prodMk continuous_id)).div_const _).sub
      continuous_const).norm
  have h3 := pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (1, u) (pureA F f φ) x * (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine hF F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), ParityOfCoefficients.mat_one_inv, Matrix.one_mul]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (z * (mat u⁻¹)ᵀ - c)
    · unfold coef
      rw [← h1 hu _ a', Matrix.mul_assoc, ← Matrix.transpose_mul, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1,
        Matrix.transpose_one, Matrix.mul_one]
    have b := hb f f₀ z
    have b' := hb f f₀ (z * (mat u⁻¹)ᵀ)
    rw [maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (1, u ^ k) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((1, u ^ k * u) : UA σ X.J × UA σ W.J) = (1, u ^ k) * (1, u) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]
end PositivityTheory.ThKEst
end
end
end

