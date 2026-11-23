module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0005
public import Development.WeilBound.ThetaLifts.LatticeBasics.DenseG
public import Development.WeilBound.ThetaLifts.LatticeBasics.DenseM
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsRealStructure
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsD
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace Dense

open GlobalTheory.CompanionTheory.CMAdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_evI (hF : IsTotallyReal F) (a : AF F) : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
    ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [Algebra.trace_prod_apply, Subsingleton.elim (evI F a).2 0, map_zero, add_zero,
    Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ _), Matrix.trace]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv IsTotallyReal.isReal) _ _ fun w => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr, Pi.basisFun_apply, Pi.mul_apply,
    Pi.single_eq_same, mul_one, Equiv.subtypeUnivEquiv_apply]
  exact congrArg Complex.re (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2 (a.1 w.1))

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul', show star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) = _ from
      Complex.conj_eq_iff_im.2 (im_extension h.1 w _)]

theorem ext_trace (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    InfinitePlace.Completion.extensionEmbedding w ((Algebra.trace (AF F) (AE F E) z).1 w) = piInf τ z + piInf τ (cA σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]; exact map_zero _
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [add_add_add_comm, ← hx, ← hy]
    exact map_add _ _ _
  | tmul a x =>
    change _ = _ + piInf τ (a ⊗ₜ[F] σ x)
    rw [trace_tmul, piInf_tmul, piInf_tmul, ← mul_add, ← map_add (f := _), ← trace_cm h,
      ← piInf_tmul, Algebra.algebraMap_eq_smul_one (A := E), ← TensorProduct.smul_tmul, piInf_tmul, map_one, mul_one,
      Algebra.smul_def, mul_comm]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem trace_symp (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (cA σ) (-1) (incM F X.J) (incM F W.J) u v)) =
      ∑ w, -(2 * (hf (X.J.map (τ w).1) (W.J.map (τ w).1) (u.map (piInf (τ w))) (v.map (piInf (τ w)))).re) := by
  rw [trace_evI h.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (v.map (cA σ)).map (piInf (τ w)) = (v.map (piInf (τ w))).map star := by
    ext i j
    exact piInf_cA h _ _
  rw [symp, ext_trace h (τ w), piInf_cA h, neg_one_mul, map_neg, hTens_tr,
    AddMonoidHom.map_trace (piInf (τ w)), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    Matrix.transpose_map, map_incM, map_incM, e, ← hf]
  simp
  ring

theorem eq_of_coord (M : Model σ X W) {u v : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (hv : At (evI F) v)
    (h1 : (fun i => evI F ((M.co.e u).1 i)) = fun i => evI F ((M.co.e v).1 i))
    (h2 : (fun i => evI F ((M.co.e u).2 i)) = fun i => evI F ((M.co.e v).2 i)) : u = v := by
  have a : ∀ {u}, At (evI F) u → ∀ c : AF F, evI F c = 0 → c • M.co.e u = 0 := fun hu c hc => by
    rw [← map_smul, hu c hc, map_zero]
  refine M.co.e.injective (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
  · rw [← lift_evI (z := (M.co.e u).1 i) fun c hc => congrFun (congrArg Prod.fst (a hu c hc)) i,
      ← lift_evI (z := (M.co.e v).1 i) fun c hc => congrFun (congrArg Prod.fst (a hv c hc)) i, congrFun h1 i]
  · rw [← lift_evI (z := (M.co.e u).2 i) fun c hc => congrFun (congrArg Prod.snd (a hu c hc)) i,
      ← lift_evI (z := (M.co.e v).2 i) fun c hc => congrFun (congrArg Prod.snd (a hv c hc)) i, congrFun h2 i]

theorem eq_of_piInf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {u v : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : At (evI F) u) (hv : At (evI F) v) (e : ∀ w, u.map (piInf (τ w)) = v.map (piInf (τ w))) : u = v := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · rw [smul_sub, at_entry hu i j c hc, at_entry hv i j c hc, sub_zero]
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

def tr (κ : Type) [Fintype κ] : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y b => linForm b y) (fun y y' b => map_add _ y y') (fun t y b => map_smul _ t y)
    (fun y b b' => by simp only [linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun t y b => by simp only [linForm_apply, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])

theorem tr_apply {κ : Type} [Fintype κ] (y b : κ → mixedEmbedding.mixedSpace F) :
    tr κ y b = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i) := linForm_apply b y

theorem exists_isGauss {B : Base F E} (M : Model σ X W) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') :
    ∃ (Q Q' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ)
      (f : SInf F (Fin n × Fin d)), (∀ x, x ≠ 0 → 0 < Q x x) ∧
      (∀ x, f x = 1 * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ))) ∧ M.IsGauss B.ψ B.emb f := by
  have h := hB.cm
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure σ h B.emb M.co.e fun w => cs (X.θ w) (W.θ w)
  have hom : ∀ p q, om (tr (Fin n × Fin d)) p q = ∑ w, -(2 * (hf (X.J.map (B.emb w).1) (W.J.map (B.emb w).1)
      ((S p).map (piInf (B.emb w))) ((S q).map (piInf (B.emb w)))).re) := fun p q => by
    have es : ∀ a b : AF F, evI F (a - b) = evI F a - evI F b := fun a b =>
      map_sub (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
    rw [← trace_symp h, M.co.form, es, map_sub, om, tr_apply, tr_apply]
    simp only [dotProduct, evI_sum, evI_mul, congrFun (sev _).1, congrFun (sev _).2]
  have hA : ∀ w, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← h.2.2.2, hX.herm]
  have hC : ∀ w, (Complex.I • W.J.map (B.emb w).1)ᴴ = Complex.I • W.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← h.2.2.2, hW.skew]
    simp
  obtain ⟨Q, Q', f, pos, hf', hv⟩ := exists_vacuum (tr (F := F) (Fin n × Fin d))
    (fun x y => by simp only [tr_apply, mul_comm]) J
    (fun p q => by
      simp only [hom, sJ, hf_cs (hX.cartan _) (hW.cartan _), Complex.neg_re, ← Finset.sum_neg_distrib, mul_neg])
    (fun p q => by simp only [hom, sJ, hf_cs_cs (hX.cartan _) (hW.cartan _)])
    (fun p hp => by
      obtain ⟨w, hw⟩ : ∃ w, (S p).map (piInf (B.emb w)) ≠ 0 := by
        by_contra hn
        push Not at hn
        have : S p = 0 := eq_of_piInf h B.emb (sAt p) (fun c _ => smul_zero c) fun w => by rw [hn]; simp
        have e := sev p
        rw [this, map_zero] at e
        exact hp (Prod.ext (e.1.symm.trans (funext fun _ => evI_zero)) (e.2.symm.trans (funext fun _ => evI_zero)))
      simp only [hom, sJ]
      refine Finset.sum_pos' (fun v _ => ?_) ⟨w, Finset.mem_univ _, ?_⟩
      · by_cases hv : (S p).map (piInf (B.emb v)) = 0
        · simp [hv, hf]
        · linarith [hf_neg (hA v) (hC v) (hX.cartan v) (hW.cartan v) hv]
      · linarith [hf_neg (hA w) (hC w) (hX.cartan w) (hW.cartan w) hw])
  refine ⟨Q, Q', f, pos, hf', fun _ => 1, fun u u' hu hu' e g g' hg hg' => ?_⟩
  let p := (fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i))
  have e1 : S p = u := eq_of_coord M (sAt p) hu (sev p).1 (sev p).2
  have e2 : u' = S (J p) := eq_of_piInf h B.emb hu' (sAt _) fun w => by
    rw [e, sJ, e1]
    simp [cs]
  rw [actsD_unique M hB.std hu hg, actsD_unique M hB.std hu' hg']
  ext x
  rw [SchwartzMap.smul_apply, dOp_apply, dOp_apply, e2, (sev _).1, (sev _).2]
  exact hv p x

theorem pol_dense {B : Base F E} (M : Model σ X W) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (T : SInf F (Fin n × Fin d) →L[ℂ] ℂ) (hT : ∀ f ∈ M.Pol B.ψ B.emb, T f = 0) : T = 0 := by
  obtain ⟨Q, Q', f, pos, hf', hG⟩ := exists_isGauss M hB hX hW
  exact schwartz_functional_eq_zero_of_dense Q Q' 1 f one_ne_zero pos hf' (M.Pol B.ψ B.emb) (Submodule.mem_sInf.2 fun _ hN => hN.1 _ hG)
    (fock_mul_linear F E σ n d X W M B.ψ B.emb hB.std) T hT

end Dense

theorem polSch : PolSch := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact Dense.pure_mem f ⟨h1, (h2.and hp.good.std).mono fun v hv => hv.1.trans hv.2⟩

theorem schToPol_of (hW : WeilConv) : SchToPol := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp h0 hz Φ hΦ
  obtain ⟨hc, hcont⟩ := hW F E σ B n d X W M χX χW om r s r' s' hp (Or.inr h0)
  have add := fun Φ Ψ => PositivityTheory.ThKG.I_add (Φ := Φ) (Ψ := Ψ) hp.weil fun Φ h => (hc Φ h).1
  funext h
  have key : ∀ Φ ∈ Submodule.span ℂ {Φ | ∃ f φ, Dense.Good φ ∧ Φ = pure (F := F) (κ := Fin n × Fin d) f φ},
      Φ ∈ schA F _ ∧ M.I om Φ h = 0 := fun Φ hΦ => by
    induction hΦ using Submodule.span_induction with
    | zero => exact ⟨zero_mem _, congrFun (PositivityTheory.ThKG.I_zero M om) h⟩
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, by rw [add _ _ hx.1 hy.1, hx.2, hy.2, add_zero]⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ _ hx.1, by rw [PositivityTheory.ThKG.I_smul, hx.2, mul_zero]⟩
    | mem x hx =>
      obtain ⟨f, φ, hφ, rfl⟩ := hx
      have hm : ∀ f, pure f φ ∈ schA F _ := fun f => Dense.pure_mem f hφ
      let T : SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
        { toFun := fun f => M.I om (pure f φ) h
          map_add' := fun f g => by
            rw [← add _ _ (hm f) (hm g)]
            exact congrArg (M.I om · h) (funext fun _ => add_mul _ _ _)
          map_smul' := fun c f => by
            rw [RingHom.id_apply, smul_eq_mul, ← PositivityTheory.ThKG.I_smul]
            exact congrArg (M.I om · h) (funext fun _ => mul_assoc _ _ _)
          cont := hcont _ (Dense.pf_mem hφ) h }
      have := Dense.pol_dense M hp.base hp.herm hp.skew T fun g hg => congrFun (hz _ (Submodule.subset_span
        ⟨g, hg, φ, hφ.1, (hφ.2.and hp.good.std).mono fun v hv => hv.1.trans hv.2.symm, rfl⟩)) h
      exact ⟨hm f, DFunLike.congr_fun this f⟩
  exact (key Φ (Dense.schA_le hΦ)).2

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.PairsL
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


variable (R Rf T) in
abbrev PiT : Type := R.Pi ⊗[ℂ] PiTensorProduct ℂ fun v : T => Rf.Pi v


variable (B M T) in
def Dat (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  f ∈ M.Pol B.ψ B.emb ∧ (∀ v, φ v ∈ SB _) ∧ ∀ v ∉ T, φ v = M.vac v


variable (B M p q T) in
def Cl : Submodule ℂ (Fn F n d × PiT R Rf T) :=
  Submodule.span ℂ {z | ∃ f φ, Dat B M T f φ ∧ z = (pure f φ, p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v))}

theorem Dat.cof {f φ} (h : Dat B M T f φ) : ∀ᶠ v in cofinite, φ v = M.vac v :=
  T.eventually_cofinite_notMem.mono h.2.2

theorem Dat.pureA (hM : M.IsGood B.ψ) {f φ} (h : Dat B M T f φ) :
    ∃ g ∈ SB (Fin n × Fin d → Af F), ∀ f' : SInf F (Fin n × Fin d), pure f' φ = pureA F f' g :=
  PositivityTheory.ThKG.pure_eq_pureA hM φ h.2.1 h.cof

theorem Dat.sch (hM : M.IsGood B.ψ) {f φ} (h : Dat B M T f φ) : pure f φ ∈ schA F _ := by
  obtain ⟨g, hg, e⟩ := h.pureA hM
  exact Submodule.subset_span ⟨f, g, hg, e f⟩

theorem gen_mem {f φ} (h : Dat B M T f φ) :
    (pure f φ, p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v)) ∈ Cl B M p q T := Submodule.subset_span ⟨f, φ, h, rfl⟩

theorem mem_cl {Φ ξ} : (Φ, ξ) ∈ Cl B M p q T ↔ ∃ (m : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, Dat B M T (f i) (φ i)) ∧ Φ = ∑ i, pure (f i) (φ i) ∧
      ξ = ∑ i, p (f i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ i v) := by
  constructor
  · intro h
    obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h
    choose f φ hd hg using fun i => (g i).2
    have e1 : ∀ i, pure (c i • f i) (φ i) = c i • pure (f i) (φ i) := fun i => funext fun x => by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hd i).1, (hd i).2⟩, ?_, ?_⟩
    · simpa [hg, e1, Prod.fst_sum] using (congrArg Prod.fst e).symm
    · simpa [hg, Prod.snd_sum, TensorProduct.smul_tmul'] using (congrArg Prod.snd e).symm
  · rintro ⟨m, f, φ, hd, rfl, rfl⟩
    rw [prod_mk_sum]
    exact Submodule.sum_mem _ fun i _ => gen_mem (hd i)

theorem cl_map (A : Fn F n d →ₗ[ℂ] Fn F n d) (Ω : PiT R Rf T →ₗ[ℂ] PiT R Rf T₁)
    (h : ∀ f φ, Dat B M T f φ →
      (A (pure f φ), Ω (p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v))) ∈ Cl B M p q T₁)
    {Φ ξ} (hz : (Φ, ξ) ∈ Cl B M p q T) : (A Φ, Ω ξ) ∈ Cl B M p q T₁ :=
  (Submodule.span_le (p := (Cl B M p q T₁).comap (A.prodMap Ω))).2 (by rintro _ ⟨f, φ, hd, rfl⟩; exact h f φ hd) hz

theorem cl_ext (hT : T ⊆ T₁) (e : (PiTensorProduct ℂ fun v : T => Rf.Pi v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T₁ => Rf.Pi v)
    (s : ∀ v, Rf.Pi v) (he : ∀ u : ∀ v, Rf.Pi v, (∀ v ∉ T, u v = s v) →
      e (PiTensorProduct.tprod ℂ fun v : T => u v) = PiTensorProduct.tprod ℂ fun v : T₁ => u v)
    (hs : ∀ v ∉ T, q v (M.vac v) = s v) {Φ ξ} (hz : (Φ, ξ) ∈ Cl B M p q T) : (Φ, e.lTensor _ ξ) ∈ Cl B M p q T₁ :=
  cl_map LinearMap.id _ (fun f φ hd => by
    rw [LinearMap.lTensor_tmul, he (fun v => q v (φ v)) fun v hv => by rw [hd.2.2 v hv, hs v hv]]
    exact gen_mem ⟨hd.1, hd.2.1, fun v hv => hd.2.2 v fun h => hv (hT h)⟩) hz


variable (R) in
def opAt (v : T) (Op : Module.End ℂ (Rf.Pi v)) : PiT R Rf T →ₗ[ℂ] PiT R Rf T :=
  LinearMap.lTensor R.Pi (PiTensorProduct.map (Function.update (fun j : T => (LinearMap.id : Rf.Pi j →ₗ[ℂ] Rf.Pi j)) v Op))

theorem cl_fin (hP : PureAct) (hM : M.IsGood B.ψ) (v : T) (A : Fn F n d →ₗ[ℂ] Fn F n d) (Op : Module.End ℂ (Rf.Pi v))
    (h : ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) A φ φ₁ ∧ Op (q v φ) = q v φ₁) {Φ ξ} (hz : (Φ, ξ) ∈ Cl B M p q T) :
    (A Φ, opAt R v Op ξ) ∈ Cl B M p q T := by
  refine cl_map A _ (fun f φ hd => ?_) hz
  obtain ⟨φ₁, s1, a1, e1⟩ := h _ (hd.2.1 v)
  have d₂ : Dat B M T f (Function.update φ v φ₁) := by
    refine ⟨hd.1, fun w => ?_, fun w hw => ?_⟩
    · by_cases hw : w = v
      · subst hw; simpa using s1
      · simpa [Function.update_of_ne hw] using hd.2.1 w
    · rw [Function.update_of_ne (fun e : w = v => hw (by rw [e]; exact v.2)), hd.2.2 w hw]
  convert gen_mem (p := p) (q := q) d₂ using 2
  · exact (hP F _ v A f φ hd.2.1 ((hd.cof.and hM.std).mono fun _ k => k.1.trans k.2)).2.2 _ a1
  · simp only [opAt, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext w
    by_cases hw : w = v
    · subst hw; simpa using e1
    · simp [Function.update_of_ne hw, Function.update_of_ne (show (w : Pl F) ≠ v from fun e => hw (Subtype.ext e))]

def finPart {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) : ℂ := ∏ᶠ v, φ v fun i => evFin F v (x i)

theorem finPart_add {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    finPart φ (x + z) = finPart φ x := by
  have e : ∀ (v : Pl F) i, evFin F v ((x + z) i) = evFin F v (x i) := fun v i => by
    have h : (1 : Af F) * (z i).2 = 0 :=
      congrArg Prod.snd (congrFun (hz ((0, 1) : Ainf F × Af F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i)
    have h3 : evFin F v (z i) = 0 := by
      show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
      rw [← one_mul (z i).2, h, map_zero]
    rw [Pi.add_apply, map_add (f := _), h3, add_zero]
  simp only [finPart, e]

theorem Dat.rest (hM : M.IsGood B.ψ) {f φ} (h : Dat B M T f φ) : Rest (evI F) f (finPart φ) := ⟨finPart_add φ, h.sch hM⟩

theorem cl_inf (hM : M.IsGood B.ψ) (A : Fn F n d →ₗ[ℂ] Fn F n d) (Op : Module.End ℂ R.Pi)
    (h : ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb, Acts (evI F) A f f₁ ∧ Op (p f) = p f₁) {Φ ξ}
    (hz : (Φ, ξ) ∈ Cl B M p q T) : (A Φ, Op.rTensor _ ξ) ∈ Cl B M p q T := by
  refine cl_map A _ (fun f φ hd => ?_) hz
  obtain ⟨f₁, s1, a1, e1⟩ := h _ hd.1
  rw [LinearMap.rTensor_tmul, e1, show A (pure f φ) = pure f₁ φ from a1 _ (hd.rest hM)]
  exact gen_mem ⟨s1, hd.2⟩

theorem loc_op (hL : LocRepEx) {χ χ' r s r' s'} (hp : IsPair B M χ χ' o r s r' s') {v : Pl F} {h : UA σ W.J}
    (hh : h ∈ UAt σ W (evFin F v)) : ∃ A : Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
      ∀ φ ∈ SB _, A φ ∈ SB _ ∧ Acts (evFin F v) (o (1, h)) φ (A φ) := by
  obtain ⟨ω, ρ, L⟩ := hL F E σ n d B Y W M o ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, _, _, hp.weil⟩ v
  have o1 : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]
  exact ⟨ω (1, h), fun φ hφ => ⟨L.pres 1 o1 h hh _ hφ, (L.acts 1 o1 h hh _ hφ _).2 rfl⟩⟩

theorem inf_op (hA : ArchOp) {χ χ' r s r' s'} (hp : IsPair B M χ χ' o r s r' s') {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ A : Module.End ℂ (SInf F (Fin n × Fin d)), ∀ f ∈ M.Pol B.ψ B.emb, A f ∈ M.Pol B.ψ B.emb ∧ Acts (evI F) (o (1, k)) f (A f) := by
  have o1 : (1 : UA σ Y.J) ∈ KInf σ Y B.emb :=
    ⟨fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero], fun w => by
      rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩
  obtain ⟨A, a1, a2⟩ := hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp 1 o1.1 k hk.1
  exact ⟨A, fun f hf => ⟨a2 o1 hk f hf, a1.2 f⟩⟩

theorem common_op {V V' P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup P] [Module ℂ P]
    {S : Submodule ℂ V} {S' : Submodule ℂ V'} {p : V →ₗ[ℂ] P} {p' : V' →ₗ[ℂ] P} (h : S.map p = ⊤) (A : S →ₗ[ℂ] V)
    (A' : S' →ₗ[ℂ] V') (e : ∀ x x', p x.1 = p' x'.1 → p (A x) = p' (A' x')) :
    ∃ Op : Module.End ℂ P, (∀ x, Op (p x.1) = p (A x)) ∧ ∀ x', Op (p' x'.1) = p' (A' x') := by
  have hq : Function.Surjective (p.domRestrict S) := fun u => by
    obtain ⟨x, h1, h2⟩ : u ∈ S.map p := h ▸ Submodule.mem_top
    exact ⟨⟨x, h1⟩, h2⟩
  obtain ⟨s, hs⟩ := (p.domRestrict S).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have k : ∀ x : S, p (A (s (p x.1))) = p (A x) := fun x => by
    have := e (s (p x.1) - x) 0 (by simpa [sub_eq_zero] using LinearMap.congr_fun hs (p x.1))
    simpa [sub_eq_zero] using this
  exact ⟨p ∘ₗ A ∘ₗ s, k, fun x' => e _ _ (LinearMap.congr_fun hs _)⟩

variable {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem fin_ops (hL : LocRepEx) (hm : IsMatched B G X om om' R Rf) {v : Pl F} {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    ∃ Op : Module.End ℂ (Rf.Pi v), (∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ ∧ Op (Rf.p v φ) = Rf.p v φ₁) ∧
      (∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → Op (Rf.p v φ) = Rf.p v φ₁) ∧
      ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ Op (Rf.p' v φ) = Rf.p' v φ₁ := by
  obtain ⟨A, hA⟩ := loc_op hL (PositivityTheory.ThKG.pairV hm.triple) hh
  obtain ⟨A', hA'⟩ := loc_op hL (PositivityTheory.ThKG.pairV' hm.triple) hh
  obtain ⟨Op, h1, h2⟩ := common_op (hm.fin.onto v) (A.domRestrict _) (A'.domRestrict (SB _)) fun x x' e =>
    hm.fin.equiv v h hh _ x.2 _ x'.2 _ (hA _ x.2).1 _ (hA' _ x'.2).1 (hA _ x.2).2 (hA' _ x'.2).2 e
  refine ⟨Op, fun φ hφ => ⟨_, (hA _ hφ).1, (hA _ hφ).2, h1 ⟨φ, hφ⟩⟩, fun φ hφ φ₁ h₁ e => ?_,
    fun φ hφ => ⟨_, (hA' _ hφ).1, (hA' _ hφ).2, h2 ⟨φ, hφ⟩⟩⟩
  obtain ⟨φ', s', e'⟩ : Rf.p v φ ∈ (SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
  rw [hm.fin.equiv v h hh _ hφ _ s' _ h₁ _ (hA' _ s').1 e (hA' _ s').2 e'.symm, ← e']
  exact h2 ⟨φ', s'⟩

theorem inf_ops (hO : ArchOp) (hm : IsMatched B G X om om' R Rf) {k : UA σ G.W.J} (hk : k ∈ KInf σ G.W B.emb) :
    ∃ Op : Module.End ℂ R.Pi,
      (∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb, Acts (evI F) (om (1, k)) f f₁ ∧ Op (R.p f) = R.p f₁) ∧
      (∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → Op (R.p f) = R.p f₁) ∧
      ∀ f ∈ G.M'.Pol B.ψ B.emb, ∃ f₁ ∈ G.M'.Pol B.ψ B.emb, Acts (evI F) (om' (1, k)) f f₁ ∧ Op (R.p' f) = R.p' f₁ := by
  obtain ⟨A, hA⟩ := inf_op hO (PositivityTheory.ThKG.pairV hm.triple) hk
  obtain ⟨A', hA'⟩ := inf_op hO (PositivityTheory.ThKG.pairV' hm.triple) hk
  obtain ⟨Op, h1, h2⟩ := common_op hm.real.quot.onto (A.domRestrict _) (A'.domRestrict (G.M'.Pol B.ψ B.emb)) fun x x' e =>
    hm.real.cpt k hk _ x.2 _ x'.2 _ _ (hA _ x.2).2 (hA' _ x'.2).2 e
  refine ⟨Op, fun f hf => ⟨_, (hA _ hf).1, (hA _ hf).2, h1 ⟨f, hf⟩⟩, fun f hf f₁ e => ?_,
    fun f hf => ⟨_, (hA' _ hf).1, (hA' _ hf).2, h2 ⟨f, hf⟩⟩⟩
  obtain ⟨f', s', e'⟩ : R.p f ∈ (G.M'.Pol B.ψ B.emb).map R.p' := hm.real.quot'.onto ▸ Submodule.mem_top
  rw [hm.real.cpt k hk _ hf _ s' _ _ e (hA' _ s').2 e'.symm, ← e']
  exact h2 ⟨f', s'⟩

theorem polMatch_iff {Φ Φ'} : PolMatch B G X R Rf Φ Φ' ↔
    ∃ T, X.T ⊆ T ∧ ∃ ξ, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T ∧ (Φ', ξ) ∈ Cl B G.M' R.p' Rf.p' T := by
  refine exists_congr fun T => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3⟩
    exact ⟨_, mem_cl.2 ⟨m, f, φ, h1, e1, rfl⟩, mem_cl.2 ⟨m', f', φ', h2, e2, e3⟩⟩
  · rintro ⟨ξ, h, h'⟩
    obtain ⟨m, f, φ, h1, e1, e3⟩ := mem_cl.1 h
    obtain ⟨m', f', φ', h2, e2, e4⟩ := mem_cl.1 h'
    exact ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3.symm.trans e4⟩

theorem enlarge (hm : IsMatched B G X om om' R Rf) (hX : X.T ⊆ T) (hT : T ⊆ T₁) : ∃ e : PiT R Rf T →ₗ[ℂ] PiT R Rf T₁,
    (∀ Φ ξ, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T → (Φ, e ξ) ∈ Cl B G.M R.p Rf.p T₁) ∧
      ∀ Φ ξ, (Φ, ξ) ∈ Cl B G.M' R.p' Rf.p' T → (Φ, e ξ) ∈ Cl B G.M' R.p' Rf.p' T₁ := by
  obtain ⟨e, he⟩ := exists_ext (X := Rf.Pi) T T₁ hT fun v => Rf.p v (G.M.vac v)
  exact ⟨_, fun _ _ => cl_ext hT e _ he fun _ _ => rfl,
    fun _ _ => cl_ext hT e _ he fun v hv => (hm.fin.sph v fun h => hv (hX h)).1.symm⟩

theorem polMatch_big (hm : IsMatched B G X om om' R Rf) {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') :
    ∃ T₀, X.T ⊆ T₀ ∧ ∀ T, T₀ ⊆ T → ∃ ξ, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T ∧ (Φ', ξ) ∈ Cl B G.M' R.p' Rf.p' T := by
  obtain ⟨T₀, hT, ξ, h1, h2⟩ := polMatch_iff.1 h
  refine ⟨T₀, hT, fun T h0 => ?_⟩
  obtain ⟨e, e1, e2⟩ := enlarge hm hT h0
  exact ⟨_, e1 _ _ h1, e2 _ _ h2⟩

theorem polMatch_add_smul (hm : IsMatched B G X om om' R Rf) {Φ Φ' Ψ Ψ'} (h : PolMatch B G X R Rf Φ Φ')
    (h' : PolMatch B G X R Rf Ψ Ψ') (c : ℂ) : PolMatch B G X R Rf (Φ + c • Ψ) (Φ' + c • Ψ') := by
  obtain ⟨T, hT, H⟩ := polMatch_big hm h
  obtain ⟨T', -, H'⟩ := polMatch_big hm h'
  obtain ⟨ξ, h1, h2⟩ := H _ (Finset.subset_union_left (s₂ := T'))
  obtain ⟨η, h3, h4⟩ := H' _ (Finset.subset_union_right (s₁ := T))
  exact polMatch_iff.2 ⟨_, hT.trans Finset.subset_union_left, ξ + c • η, add_mem h1 (Submodule.smul_mem _ c h3),
    add_mem h2 (Submodule.smul_mem _ c h4)⟩

end GlobalTheory.ThK.Dbl.Prs

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.StdExOf
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def StdEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∃ b K a, IsFrame2 σ Y b ∧ IsStdK (σ := σ) (Y := Y) B b K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x

theorem stdEx_of (h1 : FrameConj) (h2 : HgtEx) : StdEx := by
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

