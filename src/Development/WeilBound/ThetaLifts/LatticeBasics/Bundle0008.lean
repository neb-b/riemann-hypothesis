module

public import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0005
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.St

open PositivityTheory.ThKG.Tow

open scoped TensorProduct Matrix Pointwise RestrictedProduct
open NumberField IsDedekindDomain Topology Filter GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem isCompact_of_units {A : Type} [Monoid A] [TopologicalSpace A] [ContinuousMul A] [T2Space A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) (K : Set H) (hK : IsClosed K) (S : Set A) (hS : IsCompact S)
    (h : ∀ k ∈ K, (k.1 : A) ∈ S ∧ ((k⁻¹).1 : A) ∈ S) : IsCompact K := by
  have e : IsClosedEmbedding (fun k : H => Units.embedProduct A k.1) :=
    Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
  have hc : IsCompact (S ×ˢ (MulOpposite.op '' S)) := hS.prod (hS.image MulOpposite.continuous_op)
  exact (e.isCompact_preimage hc).of_isClosed_subset hK fun k hk => ⟨(h k hk).1, _, (h k hk).2, rfl⟩

theorem cartan_bound {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) :
    ∃ R : ℝ, ∀ A : Matrix (Fin n) (Fin n) ℂ, Aᵀ * M * A.map star = M → Commute A θ → ∀ i j, ‖A i j‖ ≤ R := by
  let Q : (Fin n → ℂ) → ℝ := fun x => ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x).re
  have hQ : Continuous Q := Complex.continuous_re.comp
    ((continuous_const.matrix_mulVec continuous_id).dotProduct (continuous_const.matrix_mulVec continuous_star))
  have hom : ∀ (t : ℝ) x, Q (t • x) = t ^ 2 * Q x := fun t x => by
    simp only [Q, star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, Complex.smul_re,
      smul_eq_mul]
    ring
  obtain ⟨c, hc, hle⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_forall_le' hQ.continuousOn (a := 0)
    fun x hx => h.2.2 x (by rintro rfl; simp at hx)
  have low : ∀ x, c * ‖x‖ ^ 2 ≤ Q x := fun x => by
    by_cases hx : x = 0
    · subst hx; simp [Q]
    · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have h1 := hle (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
      have h2 : Q x = ‖x‖ ^ 2 * Q (‖x‖⁻¹ • x) := by rw [← hom, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [h2, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  refine ⟨∑ j, √(Q (Pi.single j 1) / c), fun A hA hc' i j => ?_⟩
  have inv : ∀ x, Q (A *ᵥ x) = Q x := fun x => by
    have e1 : star (A *ᵥ x) = A.map star *ᵥ star x := by
      ext k; simp [Matrix.mulVec, dotProduct]
    have e2 : θ *ᵥ A *ᵥ x = A *ᵥ θ *ᵥ x := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc'.eq]
    have e3 : (A *ᵥ θ *ᵥ x) ⬝ᵥ M *ᵥ A.map star *ᵥ star x = (θ *ᵥ x) ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ star x := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (θ *ᵥ x) Aᵀ,
        Matrix.vecMul_transpose]
    simp only [Q]
    rw [e1, e2, e3, hA]
  have h1 : ‖A i j‖ ≤ ‖A *ᵥ Pi.single j 1‖ := by
    have := norm_le_pi_norm (A *ᵥ Pi.single j 1) i
    rwa [Matrix.mulVec_single_one] at this ⊢
  have h2 : ‖A *ᵥ Pi.single j 1‖ ≤ √(Q (Pi.single j 1) / c) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hc, mul_comm, ← inv]
    exact low _
  exact h1.trans (h2.trans (Finset.single_le_sum (f := fun j => √(Q (Pi.single j 1) / c))
    (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ j)))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem ae_ring : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem ae_t2 : T2Space (AE F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact e.isEmbedding.t2Space

theorem ae_smul : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _

attribute [local instance] ae_ring ae_t2 ae_smul

theorem evI_eq_zero {a : AF F} : evI F a = 0 ↔ a.1 = 0 := map_eq_zero_iff _ (RingEquiv.injective _)


variable (F) in
def intF : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨evI_eq_zero.2 rfl, fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨evI_eq_zero.2 (by
      change a.1 + b.1 = 0
      rw [evI_eq_zero.1 ha.1, evI_eq_zero.1 hb.1, add_zero]),
    fun v => by
      rw [map_add (evFin F v)]
      exact add_mem (ha.2 v) (hb.2 v)⟩
  neg_mem' := fun {a} ha => ⟨evI_eq_zero.2 (by
      change -a.1 = 0
      rw [evI_eq_zero.1 ha.1, neg_zero]),
    fun v => by rw [map_neg]; exact neg_mem (ha.2 v)⟩

theorem isCompact_intF : IsCompact (intF F : Set (AF F)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  let s : (∀ v : Pl F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))) → Af F :=
    RestrictedProduct.structureMap (fun v : Pl F => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  haveI : ∀ v : Pl F, CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := this
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  have hc : Continuous fun x => pairA F 0 (s x) := continuous_const.prodMk hs
  convert isCompact_range hc using 1
  ext a
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ⟨_, h2 v⟩, Prod.ext (evI_eq_zero.1 h1).symm ?_⟩
    exact RestrictedProduct.ext _ _ fun v => rfl
  · rintro ⟨x, rfl⟩
    exact ⟨evI_eq_zero.2 rfl, fun v => (x v).2⟩

theorem mem_latHat (X : Spc F E n) {a : AF F} (ha : a ∈ intF F) {y : Fin n → E} (hy : y ∈ X.L) :
    a • incV F y ∈ latHat X :=
  AddSubgroup.subset_closure ⟨a, ha.1, ha.2, y, hy, rfl⟩

theorem isCompact_latHat (X : Spc F E n) (hX : X.L.FG) : IsCompact (latHat X : Set (Fin n → AE F E)) := by
  have hZ : (X.L.restrictScalars ℤ).FG := hX.restrictScalars
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hsL : ∀ j, s j ∈ X.L := fun j => by
    have : s j ∈ X.L.restrictScalars ℤ := hs ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  haveI : CompactSpace (intF F) := isCompact_iff_compactSpace.1 isCompact_intF
  let f : (Fin m → intF F) →+ (Fin n → AE F E) :=
    AddMonoidHom.mk' (fun a => ∑ j, (a j : AF F) • incV F (s j)) fun a b => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : ((a + b) j : AF F) = a j + b j := rfl
      rw [this, add_smul]
  have hf : Continuous f := by
    change Continuous fun a : Fin m → intF F => ∑ j, (a j : AF F) • incV F (s j)
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun a : Fin m → intF F => (a j : AF F) := Continuous.subtype_val (continuous_apply j)
    exact h1.fun_smul continuous_const
  have e : latHat X = f.range := by
    refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨a, ha, ha', y, hy, rfl⟩
      have hy' : y ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
      refine ⟨fun j => c j • ⟨a, ha, ha'⟩, funext fun i => ?_⟩
      change (∑ j, (c j • a) • incV F (s j)) i = a • inclR (F := F) (AF F) ((∑ j, c j • s j) i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      change (c j • a) • inclR (F := F) (AF F) (s j i) = _
      rw [Pi.smul_apply, map_zsmul, smul_assoc, smul_comm]
    · rintro _ ⟨a, rfl⟩
      change (∑ j, (a j : AF F) • incV F (s j)) ∈ latHat X
      exact sum_mem fun j _ => mem_latHat X (a j).2 (hsL j)
  rw [e, AddMonoidHom.coe_range]
  exact isCompact_range hf


variable (F) in
def eF : AF F := pairA F 0 1

theorem eF_mem : eF F ∈ intF F := ⟨evI_eq_zero.2 rfl, fun v => by
  have : evFin F v (eF F) = 1 := map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
  rw [this]; exact one_mem _⟩

theorem vec_bound (X : Spc F E n) (hX : X.L.IsFullLattice E) (x : Fin n → E) :
    ∃ C : Set (Fin n → AE F E), IsCompact C ∧ ∀ M : Matrix (Fin n) (Fin n) (AE F E),
      (∀ y ∈ latHat X, M *ᵥ y ∈ latHat X) → M *ᵥ (eF F • incV F x) ∈ C := by
  have hx : x ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
    rw [hX.span_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨_, isCompact_latHat X hX.fg, fun M hM => hM _ (mem_latHat X eF_mem hy)⟩
  | zero =>
    refine ⟨{0}, isCompact_singleton, fun M _ => ?_⟩
    have : incV F (0 : Fin n → E) = 0 := funext fun i => map_zero (inclR (F := F) (AF F))
    rw [this, smul_zero, Matrix.mulVec_zero]; rfl
  | add y z _ _ hy hz =>
    obtain ⟨C, hC, h⟩ := hy
    obtain ⟨C', hC', h'⟩ := hz
    refine ⟨C + C', hC.add hC', fun M hM => ?_⟩
    have : incV F (y + z) = incV F y + incV F z := funext fun i => map_add (inclR (F := F) (AF F)) _ _
    rw [this, smul_add, Matrix.mulVec_add]
    exact Set.add_mem_add (h M hM) (h' M hM)
  | smul c y _ hy =>
    obtain ⟨C, hC, h⟩ := hy
    refine ⟨(fun z => inclR (F := F) (AF F) c • z) '' C, hC.image (continuous_const_smul _), fun M hM => ⟨_, h M hM, ?_⟩⟩
    have : eF F • incV F (c • y) = inclR (F := F) (AF F) c • eF F • incV F y :=
      funext fun i => by
        change eF F • inclR (F := F) (AF F) (c * y i) = inclR (F := F) (AF F) c * (eF F • inclR (F := F) (AF F) (y i))
        rw [map_mul, mul_smul_comm]
    rw [this]
    exact (Matrix.mulVec_smul _ _ _).symm

theorem fin_bound (X : Spc F E n) (hX : X.L.IsFullLattice E) (i j : Fin n) :
    ∃ C : Set (AE F E), IsCompact C ∧ ∀ M : Matrix (Fin n) (Fin n) (AE F E),
      (∀ y ∈ latHat X, M *ᵥ y ∈ latHat X) → eF F • M i j ∈ C := by
  obtain ⟨C, hC, h⟩ := vec_bound X hX (Pi.single j 1)
  refine ⟨(fun z => z i) '' C, hC.image (continuous_apply i), fun M hM => ⟨_, h M hM, ?_⟩⟩
  have : incV F (Pi.single j 1 : Fin n → E) = Pi.single j 1 := funext fun k => by
    by_cases hk : k = j
    · subst hk; simp [incV]
    · simp [incV, hk]
  rw [this, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

omit [NumberField E] in
theorem piInf_smul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (z : AE F E) :
    piInf τ (a • z) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * piInf τ z := by
  have : piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    change InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 1 = _
    rw [map_one, mul_one]
  rw [Algebra.smul_def, map_mul, this]

omit [NumberField E] in
theorem compFin_smul (v : Pl F) {a : AF F} (ha : a.2 = 0) (z : AE F E) : compFin F E v (a • z) = 0 := by
  have : compFin F E v (algebraMap (AF F) (AE F E) a) = 0 := by
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a.2 ⊗ₜ[F] (1 : E) = 0
    rw [ha, map_zero, TensorProduct.zero_tmul]
  rw [Algebra.smul_def, map_mul, this, zero_mul]

theorem exists_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ Φ : (InfinitePlace F → ℂ) → AE F E, Continuous Φ ∧ ∀ z, z = Φ (fun w => piInf (τ w) z) + eF F • z := by
  haveI := h.1
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  let ρ : (InfinitePlace F → ℝ) → AF F := fun t =>
    pairA F (fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w)) 0
  have hρ : Continuous ρ := by
    have : Continuous fun (t : InfinitePlace F → ℝ) (w : InfinitePlace F) =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w) :=
      continuous_pi fun w => (IsometryEquiv.continuous _).comp (continuous_apply w)
    exact this.prodMk continuous_const
  have eρ : ∀ t w, InfinitePlace.Completion.extensionEmbedding w ((ρ t).1 w) = t w := fun t w => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hr w)]
    exact congrArg _ ((InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).apply_symm_apply (t w))
  obtain ⟨a, ha, -⟩ := Levi.exists_inf h τ fun _ => Complex.I
  refine ⟨fun z => ρ (fun w => (z w).re) • 1 + ρ (fun w => (z w).im) • a, ?_, fun z => ?_⟩
  · have h1 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).re :=
      hρ.comp (continuous_pi fun w => Complex.continuous_re.comp (continuous_apply w))
    have h2 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).im :=
      hρ.comp (continuous_pi fun w => Complex.continuous_im.comp (continuous_apply w))
    have h3 : ∀ b : AE F E, Continuous fun x : AF F => x • b := fun b =>
      Continuous.fun_smul (f := fun x : AF F => x) (g := fun _ => b) continuous_id' continuous_const
    exact Continuous.fun_add (f := fun z : InfinitePlace F → ℂ => ρ (fun w => (z w).re) • (1 : AE F E))
      (g := fun z => ρ (fun w => (z w).im) • a) ((h3 1).comp' h1) ((h3 a).comp' h2)
  · refine Levi.ad_ext h τ (fun w => ?_) fun v => ?_
    · have e0 : (eF F).1 w = 0 := rfl
      rw [map_add (f := _), map_add (f := _), piInf_smul, piInf_smul, piInf_smul, eρ, eρ, ha, e0, map_zero, map_one, zero_mul, mul_one,
        add_zero, Complex.re_add_im]
    · have e0 : compFin F E v ((1 - eF F) • z) = 0 := compFin_smul v (sub_self (1 : Af F)) z
      rw [sub_smul, one_smul, map_sub, sub_eq_zero] at e0
      rw [map_add (f := _), map_add (f := _), compFin_smul v rfl, compFin_smul v rfl, zero_add, zero_add, e0]

end GlobalTheory.ThK.Dbl.St

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.NonZero
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩

theorem res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {m n k : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' n)
    (e : k = m + n) : ResEtaPow K (χ / χ') k := fun x => by
  rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

theorem pairV (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    res_div h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem pairV' (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    res_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem split_zero {W : Spc F E (a + a')} {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (X : Chars F E) :
    Split2 (σ := σ) (W := W) W₁ H' X 0 0 0 :=
  ⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩

theorem big_of (hB : NonZeroBot) (hT : TowerB) (hE : EvZero) (hC : CTBigZero) (hS : SchToPol) (hP : PolSch) (hL : LeviEx) (q : ℕ) :
    ∀ (a' : ℕ) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = 0 → G.q = q →
      ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  induction q with
  | zero => exact fun a' G om om' h hp hq => (hB F E σ B a a' G X om om' h hp hq).1
  | succ q ih =>
    intro a' G om om' h hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := h.geo.aBig; omega⟩
    obtain ⟨V, V', W, h', G₁, H, H', c, om₁, om₁', h₁⟩ := hT F E σ B a b G X om om' h (by omega)
    obtain ⟨Φ₁, p1, n1⟩ := ih b G₁ om₁ om₁' h₁ (c.ep.trans hp) (by have : G₁.q + 1 = G.q := c.eq; omega)
    obtain ⟨⟨e, he⟩, he'⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h') _ G₁.V G₁.W H' _ _ G₁.M c.eV c.hH' h₁.geo.hM
    obtain ⟨Φ, p2, rfl⟩ := Submodule.mem_map.1 ((he' e he).ge p1)
    obtain ⟨C, hC0, hc⟩ := hC F E σ B a b _ G₁ H H' c e he
    by_contra hn
    push Not at hn
    have z : G.M.I om Φ = 0 := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h) (by omega) hn Φ
      (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h') Φ p2)
    refine n1 (funext fun g => ?_)
    obtain ⟨m, hm⟩ := hL F E σ B _ _ _ _ H' _ _ _ _ h.base h'.geo.hW c.hH' g
    have := hc X om om' om₁ om₁' h' h₁ Φ p2 0 0 (by
      show Split2 _ _ _ (G.M.I om Φ) 0 0
      rw [z]; exact split_zero _ _ _) g m hm 1
    have o : om (1, 1) Φ = Φ := DFunLike.congr_fun (map_one om) Φ
    erw [o] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hC0

theorem small_of (hB : NonZeroBot) (hT : TowerA) (hE : EvZero) (hC : CTSmallZero) (hS : SchToPol) (hP : PolSch) (hL : LeviEx)
    (hZ : SplitEx) (p : ℕ) :
    ∀ (a : ℕ) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = p → G.q = 0 →
      ∃ Φ ∈ PolData B G.M', G.M'.I om' Φ ≠ 0 := by
  induction p with
  | zero => exact fun a G om om' h hp hq => (hB F E σ B a a' G X om om' h hp hq).2
  | succ p ih =>
    intro a G om om' h hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by have := h.geo.aBig; have := h.geo.lt; omega⟩
    obtain ⟨V, V', W, h', G₁, H, H', c, om₁, om₁', h₁⟩ := hT F E σ B b a' G X om om' h hq (by omega)
    obtain ⟨Φ₁, p1, n1⟩ := ih b G₁ om₁ om₁' h₁ (by have : G₁.p + 1 = G.p := c.ep; omega) c.q1
    obtain ⟨⟨e, he⟩, he'⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h') _ G₁.V' G₁.W H' _ _ G₁.M' c.eV c.hH' h₁.geo.hM'
    obtain ⟨Φ, p2, rfl⟩ := Submodule.mem_map.1 ((he' e he).ge p1)
    obtain ⟨C, hC0, hc⟩ := hC F E σ B b a' _ G₁ H H' c e he
    by_contra hn
    push Not at hn
    have z : G.M'.I om' Φ = 0 := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h) (by omega) hn Φ
      (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h') Φ p2)
    refine n1 (funext fun g => ?_)
    obtain ⟨m, hm⟩ := hL F E σ B _ _ _ _ H' _ _ _ _ h.base h'.geo.hW c.hH' g
    obtain ⟨fa, s1, s2⟩ := hc X om om' om₁ om₁' h' h₁ Φ p2
    have s3 : Split2 G₁.W H' X (G.M'.I om' Φ) fa 0 := s1
    rw [z] at s3
    have i0 : (reG G V V' W).M.I om 0 = 0 := funext fun x => by simp [Model.I, theta, thetaSum]
    have fz : fa = 0 := congrArg Prod.fst (((hZ F E σ B _ _ (reG G V V' W) X om om' h' _ G₁.W H' _ _ c.hH').1 0 (zero_mem _)).unique
      (y₁ := (fa, 0)) (y₂ := (0, 0)) (by rw [i0]; exact s3) (by rw [i0]; exact split_zero _ _ _))
    have := s2 g m hm 1
    have o : om' (1, 1) Φ = Φ := DFunLike.congr_fun (map_one om') Φ
    erw [fz, o] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hC0

theorem nonZeroAn_of (hB : NonZeroBot) (hA : TowerA) (hT : TowerB) (hE : EvZero) (hC : CTBigZero) (hC' : CTSmallZero)
    (hS : SchToPol) (hP : PolSch) (hL : LeviEx) (hZ : SplitEx) (hO : ToSo) : NonZeroAn := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  refine ⟨fun hp => big_of hB hT hE hC hS hP hL _ a' G om om' h hp rfl, fun hq => ?_⟩
  obtain ⟨Φ, p1, n1⟩ := small_of hB hA hE hC' hS hP hL hZ _ a G om om' h rfl hq
  obtain ⟨Ψ, p2, e⟩ := hO F E σ B a a' G X om om' h hq Φ p1
  exact ⟨Ψ, p2, e ▸ n1⟩

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.SWFull
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem mero_eq {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) {e g : ℂ → ℂ} (he : MeromorphicOn e Set.univ)
    (hg : DifferentiableOn ℂ g U) {t : ℝ} (h : ∀ s : ℂ, t < s.re → s ∈ U ∧ e s = g s) {s : ℂ} (hs : s ∈ U) (hc' : ContinuousAt e s) :
    e s = g s := by
  have ha := hg.analyticOnNhd hU
  have m : MeromorphicOn (e - g) U := (he.mono_set (Set.subset_univ _)).sub ha.meromorphicOn
  have h1 : t < ((t + 1 : ℝ) : ℂ).re := by simp
  have z : meromorphicOrderAt (e - g) s = ⊤ := by
    by_contra hne
    refine m.meromorphicOrderAt_ne_top_of_isPreconnected hc hs (h _ h1).1 hne (meromorphicOrderAt_eq_top_iff.2 ?_)
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1)] with z hz
    exact sub_eq_zero.2 (h z hz).2
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] s) (hc'.mono_left nhdsWithin_le_nhds)
    ((ha s hs).continuousAt.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 z] with z hz using sub_eq_zero.1 hz

theorem contAt_of_sphere {X : Type} [TopologicalSpace X] {g : ℂ → X → ℂ} {s₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ∀ x, DiffContOnCl ℂ (g · x) (Metric.ball s₀ ρ))
    (hc : ContinuousOn (fun y : ℂ × X => g y.1 y.2) (Metric.sphere s₀ ρ ×ˢ Set.univ)) (x₀ : X) :
    ContinuousAt (fun y : ℂ × X => g y.1 y.2) (s₀, x₀) := by
  have c0 : ContinuousAt (g · x₀) s₀ := ((hd x₀).differentiableAt Metric.isOpen_ball (Metric.mem_ball_self hρ)).continuousAt
  have : Tendsto (fun y : ℂ × X => g y.1 y.2 - g y.1 x₀) (𝓝 (s₀, x₀)) (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have c1 : Continuous fun y : X × Metric.sphere s₀ ρ => ‖g y.2 y.1 - g y.2 x₀‖ :=
      ((hc.comp_continuous (f := fun y : X × Metric.sphere s₀ ρ => (y.2.1, y.1)) (by fun_prop) fun y => ⟨y.2.2, trivial⟩).sub
        (hc.comp_continuous (f := fun y : X × Metric.sphere s₀ ρ => (y.2.1, x₀)) (by fun_prop) fun y => ⟨y.2.2, trivial⟩)).norm
    have e1 : ∀ᶠ x in 𝓝 x₀, ∀ z ∈ (Set.univ : Set (Metric.sphere s₀ ρ)), ‖g z x - g z x₀‖ < ε / 2 :=
      isCompact_univ.eventually_forall_of_forall_eventually fun z _ =>
        (isOpen_lt c1 continuous_const).mem_nhds (by simpa using hε)
    filter_upwards [prod_mem_nhds (Metric.ball_mem_nhds s₀ hρ) e1] with y hy
    rw [dist_zero_right]
    refine (Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball ((hd y.2).sub (hd x₀)) (C := ε / 2)
      (fun z hz => ?_) (subset_closure hy.1)).trans_lt (half_lt_self hε)
    rw [frontier_ball _ hρ.ne'] at hz
    exact (hy.2 ⟨z, hz⟩ trivial).le
  have h2 := this.add (c0.tendsto.comp continuous_fst.continuousAt)
  simpa [ContinuousAt] using h2

theorem IsEisCont.update {f : ℂ → G2 σ Y → ℂ} {U : Set ℂ} {Ê : ℂ → G2 σ Y → ℂ} (h : IsEisCont f U Ê) {s₀ : ℂ} {k : ℕ}
    (hr : IsRegAt Ê s₀ k) {val : G2 σ Y → ℂ} (hv : EisValueAt f s₀ val) :
    IsEisCont f (insert s₀ U) (Function.update Ê s₀ val) := by
  obtain ⟨r, H, r0, hH, -, -, C, N, hC⟩ := hr
  obtain ⟨t, half⟩ := h.half
  have op : IsOpen (insert s₀ U) := isOpen_iff_mem_nhds.2 fun s hs => hs.elim
    (fun e => e ▸ insert_mem_nhds_iff.2 (h.disc s)) fun hs => mem_of_superset (h.isOpen.mem_nhds hs) (Set.subset_insert _ _)
  have ev : ∀ s ≠ s₀, ∀ᶠ z in 𝓝 s, Function.update Ê s₀ val z = Ê z := fun s hs => by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz using Function.update_of_ne hz _ _
  have hol : ∀ x, DifferentiableOn ℂ (Function.update Ê s₀ val · x) (insert s₀ U) := fun x s hs => by
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases e0 : s = s₀
    · obtain ⟨e, he, ⟨t', h1⟩, h2, h3⟩ := hv x
      subst e0
      refine h2.differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [h2.eventually_analyticAt, op.mem_nhds hs] with z hz hz'
      by_cases e1 : z = s
      · rw [e1, Function.update_self, h3]
      · rw [Function.update_of_ne e1]
        exact (mero_eq h.isOpen h.conn he (h.hol x) (t := max t t') (fun s hs => ⟨(half s (max_lt_iff.1 hs).1).1,
          (h1 s (max_lt_iff.1 hs).2).unique ((half s (max_lt_iff.1 hs).1).2 x)⟩)
          (hz'.resolve_left e1) hz.continuousAt).symm
    · exact ((h.hol x).differentiableAt (h.isOpen.mem_nhds (hs.resolve_left e0))).congr_of_eventuallyEq
        ((ev s e0).mono fun z hz => congrFun hz x)
  obtain ⟨ρ, ρ0, hρ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (inter_mem (op.mem_nhds (Set.mem_insert _ _)) (Metric.ball_mem_nhds s₀ r0))
  have dc : ∀ x, DiffContOnCl ℂ (Function.update Ê s₀ val · x) (Metric.ball s₀ ρ) := fun x =>
    (hol x).diffContOnCl_ball fun z hz => (hρ hz).1
  have sp : ∀ z ∈ Metric.sphere s₀ ρ, z ≠ s₀ := fun z hz => Metric.ne_of_mem_sphere hz ρ0.ne'
  have ca : ∀ s ∈ U, s ≠ s₀ → ∀ x, ContinuousAt (fun y : ℂ × G2 σ Y => Function.update Ê s₀ val y.1 y.2) (s, x) := fun s hs e x =>
    (h.cont.continuousAt (prod_mem_nhds (h.isOpen.mem_nhds hs) univ_mem)).congr
      ((continuous_fst.continuousAt.eventually (ev s e)).mono fun y hy => (congrFun hy y.2).symm)
  refine ⟨op, h.conn.subset_closure (Set.subset_insert _ _) (Set.insert_subset ?_ subset_closure),
    fun s => (h.disc s).mono fun z hz => .inr hz, ⟨max t s₀.re, fun s hs => ⟨.inr (half s (max_lt_iff.1 hs).1).1, fun x => ?_⟩⟩, hol, fun y hy => ?_, fun s hs => ?_⟩
  · exact mem_closure_iff_frequently.2 ((h.disc s₀).frequently.filter_mono nhdsWithin_le_nhds)
  · rw [Function.update_of_ne fun e => (max_lt_iff.1 hs).2.ne (by rw [e])]; exact (half s (max_lt_iff.1 hs).1).2 x
  · refine ContinuousAt.continuousWithinAt ?_
    by_cases e0 : y.1 = s₀
    · rw [show y = (s₀, y.2) from Prod.ext e0 rfl]
      exact contAt_of_sphere ρ0 dc (fun z hz => (ca z.1 ((hρ (Metric.sphere_subset_closedBall hz.1)).1.resolve_left (sp _ hz.1))
        (sp _ hz.1) z.2).continuousWithinAt) _
    · exact ca y.1 (hy.1.resolve_left e0) e0 y.2
  · by_cases e0 : s = s₀
    · subst e0
      refine ⟨ρ, C / ρ ^ k, N, ρ0, fun z hz x => Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball (dc x)
        (fun w hw => ?_) (subset_closure hz)⟩
      rw [frontier_ball _ ρ0.ne'] at hw
      have b := (hρ (Metric.sphere_subset_closedBall hw)).2
      have := hC w b x
      rw [hH w b (sp w hw), norm_mul, norm_pow, mem_sphere_iff_norm.1 hw] at this
      rw [Function.update_of_ne (sp w hw), div_mul_eq_mul_div, le_div_iff₀' (pow_pos ρ0 k)]
      exact this
    · obtain ⟨ε, C', N', ε0, hb⟩ := h.grow s (hs.resolve_left e0)
      obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (inter_mem (ev s e0) (Metric.ball_mem_nhds s ε0))
      exact ⟨δ, C', N', δ0, fun z hz x => by rw [(hδ hz).1]; exact hb z (hδ hz).2 x⟩

theorem swFull_of (h1 : SWAniso) (h2 : EisContinues) (h3 : BoxSec) : SWFull := by
  intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n Y r' s' hB hn (.inr hY) χ hχ m hr K a hK ha _ _
    (h3 F E σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((m : ℂ) - n) / 2)
  exact ⟨_, _, hE.update hk (h1 F E σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩

end GlobalTheory.ThK.Dbl

end
end

