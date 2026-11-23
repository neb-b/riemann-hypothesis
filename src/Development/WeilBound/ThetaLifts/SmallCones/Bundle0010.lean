module

public import Development.WeilBound.ThetaLifts.SmallCones.Bundle0008
public import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg
public import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
public import Development.WeilBound.ThetaLifts.SmallCones.KerPol

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.KFinArch
section
noncomputable section

namespace PositivityTheory.ThKCT.So

open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKOwn.KPol GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD PositivityTheory.ThKG.Tow.Levi
open scoped TensorProduct Classical Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem exists_at_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ) :
    ∃ a : AE F E, At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := by
  choose b hb using fun w => (infEmb_bijective h (τ w)).2 (z w)
  refine ⟨∑ w, TensorProduct.map (sgI w) LinearMap.id (b w), fun s hs => ?_, fun w => ?_⟩
  · have h1 : s.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hs
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    induction b w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : s * sgI w a = 0 := Prod.ext (show s.1 * _ = 0 by rw [h1, zero_mul]) (show s.2 * 0 = 0 from mul_zero _)
      rw [TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul, this, TensorProduct.zero_tmul]
    | add x y hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [piInf, RingHom.comp_apply, map_sum, Finset.sum_eq_single w (fun u _ hu => compInf_sgI_ne hu.symm _)
      (fun h => absurd (Finset.mem_univ w) h), compInf_sgI_self, hb]

theorem exists_mat_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) :
    ∃ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => exists_at_inf h τ (fun w => z w i j)
  exact ⟨Matrix.of a, fun x hx => Matrix.ext fun i j => (ha i j).1 x hx, fun w => Matrix.ext fun i j => (ha i j).2 w⟩


variable (F) in
def lamF (κ : Type) [Fintype κ] : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ where
  toFun := linForm
  map_add' a b := by
    ext y
    simp only [linForm_apply, ContinuousLinearMap.add_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' c a := by
    ext y
    simp [linForm_apply, ← Finset.smul_sum]

theorem lamF_inj (κ : Type) [Fintype κ] : Function.Injective (lamF F κ) := by
  refine (injective_iff_map_eq_zero _).2 fun l h => funext fun i => ?_
  refine (mixedEmbedding.latticeBasis F).ext_elem fun j => ?_
  have h1 : linForm l (Pi.single i (mixedEmbedding F ((integralBasis F).traceDual j))) = 0 := DFunLike.congr_fun h _
  rw [linForm_apply, Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same, mul_comm,
    ← (mixedEmbedding.latticeBasis F).sum_repr (l i)] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, mixedEmbedding.latticeBasis_apply, ← map_mul, GlobalTheory.LatVacArith.trace_mixedEmbedding,
    Module.Basis.trace_mul_traceDual] at h1
  simpa [apply_ite] using h1

variable (M : Model σ X W) {ψ : AddChar (AF F) ℂ}

def ph (u : Matrix (Fin n) (Fin d) (AE F E)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  (aOf M u, fun i => evI F ((M.co.e u).2 i))

theorem dopL_ph (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    dopL (lamF F _) (ph M u) f = dop (aOf M u) (lOf M u) f := rfl

theorem exists_ph (p) : ∃ u, At (evI F) u ∧ ph M u = p := by
  have hat : ∀ (ξ : Fin n × Fin d → mixedEmbedding.mixedSpace F) (s : AF F), evI F s = 0 → s • pt ξ 0 = 0 := fun ξ s hs => by
    have h1 : s.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hs
    funext i
    exact Prod.ext (show s.1 * _ = 0 by rw [h1, zero_mul]) (show s.2 * 0 = 0 from mul_zero _)
  refine ⟨M.co.e.symm (pt p.1 0, pt p.2 0), fun s hs => ?_, ?_⟩
  · rw [← map_smul, LinearEquiv.map_eq_zero_iff]
    exact Prod.ext (hat _ s hs) (hat _ s hs)
  · unfold ph aOf
    rw [LinearEquiv.apply_symm_apply, evI_pt, evI_pt]

def Rel (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  At (evI F) u ∧ At (evI F) u' ∧
    ∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)

def vacE (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  vacs (lamF F _) {γ | ∃ u u', Rel (X := X) (W := W) τ ε u u' ∧ γ = (ph M u, ph M u')}

theorem mem_vacE {τ : ∀ w : InfinitePlace F, EmbOver E w} {ε : InfinitePlace F → ℤˣ} {f : SInf F (Fin n × Fin d)} :
    f ∈ vacE M τ ε ↔ ∀ u u', Rel (X := X) (W := W) τ ε u u' →
      dop (aOf M u') (lOf M u') f = Complex.I • dop (aOf M u) (lOf M u) f := by
  rw [vacE, mem_vacs]
  constructor
  · intro h u u' hu
    rw [← dopL_ph, ← dopL_ph]
    exact h (ph M u, ph M u') ⟨u, u', hu, rfl⟩
  · rintro h _ ⟨u, u', hu, rfl⟩
    rw [dopL_ph, dopL_ph]
    exact h u u' hu

theorem vacE_fin (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) :
    FiniteDimensional ℂ (vacE M τ ε) := by
  refine vacs_fin _ (lamF_inj _) _ fun p => ?_
  obtain ⟨u, hu, rfl⟩ := exists_ph M p
  obtain ⟨u', hu', e⟩ := exists_mat_inf h τ fun w => (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)
  exact ⟨_, ⟨u, u', ⟨hu, hu', e⟩, rfl⟩, rfl⟩

def polM (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : ℕ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  fil (⨆ ε, vacE M τ ε) (fun i => dopL (lamF F _) (Module.finBasis ℝ _ i)) m

theorem polM_fin (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : ℕ) : FiniteDimensional ℂ (polM M τ m) := by
  haveI := vacE_fin M h τ
  exact fil_fin _ _ m

theorem exists_polM (hψ : IsStd ψ) {τ : ∀ w : InfinitePlace F, EmbOver E w} {f} (hf : f ∈ M.Pol ψ τ) : ∃ m, f ∈ polM M τ m := by
  have hd : Directed (· ≤ ·) (polM M τ) := (fil_mono _ _).directed_le
  rw [← Submodule.mem_iSup_of_directed _ hd]
  refine (sInf_le ⟨fun f₀ ⟨ε, hε⟩ => ?_, fun u hu f hf f₁ h => ?_⟩ : M.Pol ψ τ ≤ ⨆ m, polM M τ m) hf
  · refine Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem ε ((mem_vacE M).2 fun u u' h => ?_))
    exact hε u u' h.1 h.2.1 h.2.2 _ _ (actsD_dop M hψ h.1 f₀) (actsD_dop M hψ h.2.1 f₀)
  · obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hd).1 hf
    rw [actsD_unique M hψ hu h, ← dopL_ph]
    exact Submodule.mem_iSup_of_mem (m + 1) (fil_step _ _ hm (dopL_mem _ _ _ _))

theorem line_slice (hψ : IsStd ψ) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (t : ℝ) {Ψ} (hΨ : Ψ ∈ schA F (Fin n × Fin d))
    (ξ) (y) : M.heisLine ψ u t Ψ (pt ξ y) = hl (aOf M u) (lOf M u) t (fun ξ' => Ψ (pt ξ' y)) ξ := by
  induction hΨ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    rw [← tens_rOf, heisLine_tens M hψ hu f (fun x z hz => rOf_add g x z hz) t, tens_rOf, tens_rOf]
    simp only [pureA_pt, hl, mul_assoc]
  | zero => simp [Model.heisLine, Darboux.rho, schr, hl]
  | add Φ Ψ _ _ h1 h2 =>
    rw [Model.heisLine, rho_add] at *
    simp only [Pi.add_apply, h1, h2, hl, mul_add]
  | smul c Φ _ h =>
    rw [Model.heisLine, rho_smul] at *
    simp only [Pi.smul_apply, h, hl, smul_eq_mul]
    ring

variable {M} {om : Rep σ X W} {x : UA σ X.J × UA σ W.J} {g : (Fin n × Fin d → Af F) → ℂ} {y : Fin n × Fin d → Af F}

theorem exists_slice (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om) (x) (hg : g ∈ SB _) (y) :
    ∃ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ (f : SInf F (Fin n × Fin d)) ξ, om x (pureA F f g) (pt ξ y) = A f ξ := by
  choose A hA using fun f : SInf F (Fin n × Fin d) =>
    slice_schwartz (hs.pres x (pureA F f g) (Submodule.subset_span ⟨f, g, hg, rfl⟩)) y
  refine ⟨{ toFun := A, map_add' := fun a b => ?_, map_smul' := fun c a => ?_ }, hA⟩
  · ext ξ
    have : pureA F (a + b : SInf F _) g = pureA F a g + pureA F b g := funext fun _ => by simp [pureA, add_mul]
    rw [SchwartzMap.add_apply, ← hA, ← hA, ← hA, this, map_add (f := _), Pi.add_apply]
  · ext ξ
    have : pureA F (c • a : SInf F _) g = c • pureA F a g := funext fun _ => by simp [pureA, mul_assoc]
    rw [RingHom.id_apply, SchwartzMap.smul_apply, ← hA, ← hA, this, map_smul, Pi.smul_apply]

theorem at_act {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (x : UA σ X.J × UA σ W.J) :
    At (evI F) (actAB (cA σ) x u) := fun s hs => by
  rw [actAB, ← Matrix.smul_mul, ← Matrix.mul_smul, hu s hs, Matrix.mul_zero, Matrix.zero_mul]

theorem inter_ne (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om) (hg : g ∈ SB _)
    {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)} (hA : ∀ (f : SInf F (Fin n × Fin d)) ξ, om x (pureA F f g) (pt ξ y) = A f ξ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (ha : aOf M u ≠ 0) (f : SInf F (Fin n × Fin d)) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M (actAB (cA σ) x u)) (lOf M (actAB (cA σ) x u)) (A f) := by
  obtain ⟨G, hG, hD⟩ := hl_line_deriv (aOf M u) (lOf M u) f
  ext ξ
  let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (pt ξ y)
  have hl' : l ∈ (adeleClass F).adm (Fin n × Fin d) := fun g' _ =>
    ⟨g' y • (BoundedContinuousFunction.evalCLM ℂ ξ ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _), fun f => by
      simp [l, pureA_pt, mul_comm]⟩
  obtain ⟨T, hT⟩ := hs.adm x l hl' g hg
  have hT' : ∀ f, A f ξ = T f := fun f => (hA f ξ).symm.trans (hT f)
  have h1 := hD ha T
  have hΦ : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e : (fun t => T (G t)) = fun t => hl (aOf M (actAB (cA σ) x u)) (lOf M (actAB (cA σ) x u)) t (A f) ξ := by
    funext t
    have e1 : M.heisLine ψ u t (pureA F f g) = pureA F (G t) g := by
      rw [← tens_rOf, heisLine_tens M hψ hu f (fun x z hz => rOf_add g x z hz) t, tens_rOf]
      congr 1
      funext x
      exact (hG t x).symm
    have e2 : om x (M.heisLine ψ u t (pureA F f g)) = M.heisLine ψ (actAB (cA σ) x u) t (om x (pureA F f g)) := by
      have := hs.impl x (realAd F t • u) _ hΦ
      rwa [show actAB (cA σ) x (realAd F t • u) = realAd F t • actAB (cA σ) x u by
        rw [actAB, actAB, Matrix.mul_smul, Matrix.smul_mul]] at this
    rw [← hT', ← hA, ← e1, e2, line_slice M hψ (at_act hu x) t (hs.pres x _ hΦ), funext (hA f)]
  rw [e] at h1
  rw [hT']
  exact h1.unique (hasDerivAt_hl _ _ (A f) ξ)

theorem inter' (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om) (hg : g ∈ SB _)
    {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)} (hA : ∀ (f : SInf F (Fin n × Fin d)) ξ, om x (pureA F f g) (pt ξ y) = A f ξ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M (actAB (cA σ) x u)) (lOf M (actAB (cA σ) x u)) (A f) := by
  by_cases ha : aOf M u = 0
  · rcases subsingleton_or_nontrivial (Fin n × Fin d → mixedEmbedding.mixedSpace F) with hV | hV
    · rw [dop_subsingleton, dop_subsingleton, map_zero]
    · obtain ⟨ξ, hξ⟩ := exists_ne (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)
      obtain ⟨v, hv, rfl⟩ := exists_at M ξ
      have huv : At (evI F) (u + v) := fun s hs => by rw [smul_add, hu s hs, hv s hs, add_zero]
      have h1 := inter_ne hψ hs hg hA huv (by rw [aOf_add, ha, zero_add]; exact hξ) f
      have h2 := inter_ne hψ hs hg hA hv hξ f
      rw [aOf_add, lOf_add, dop_add, map_add (f := _), show actAB (cA σ) x (u + v) = actAB (cA σ) x u + actAB (cA σ) x v by
        rw [actAB, actAB, actAB, Matrix.mul_add, Matrix.add_mul], aOf_add, lOf_add, dop_add, h2] at h1
      exact add_right_cancel h1
  · exact inter_ne hψ hs hg hA hu ha f

theorem polM_stab (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om) (hg : g ∈ SB _)
    {τ : ∀ w : InfinitePlace F, EmbOver E w} {k : UA σ X.J} (hk : ∀ w, Commute ((mat k⁻¹).map (piInf (τ w))) (X.θ w))
    {A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)} (hA : ∀ (f : SInf F (Fin n × Fin d)) ξ, om (k, 1) (pureA F f g) (pt ξ y) = A f ξ) (m : ℕ)
    {f} (hf : f ∈ polM M τ m) : A f ∈ polM M τ m := by
  refine fil_stab _ _ A (fun f hf => ?_) (fun i f => ?_) m hf
  · refine (iSup_le fun ε f hf => ?_ : _ ≤ (⨆ ε, vacE M τ ε).comap A) hf
    refine Submodule.mem_iSup_of_mem ε ((mem_vacE M).2 fun u u' h => ?_)
    have hat : ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) (mat k⁻¹ * u) := fun u hu s hs => by
      rw [← Matrix.mul_smul, hu s hs, Matrix.mul_zero]
    have e : ∀ u : Matrix (Fin n) (Fin d) (AE F E), actAB (cA σ) ((k, 1) : UA σ X.J × UA σ W.J) (mat k⁻¹ * u) = u := fun u => by
      change mat k * (mat k⁻¹ * u) * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = u
      rw [← Matrix.mul_assoc, mat_mul_inv, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    have i1 := inter' hψ hs hg hA (hat u h.1) f
    have i2 := inter' hψ hs hg hA (hat u' h.2.1) f
    rw [e] at i1 i2
    rw [← i1, ← i2, (mem_vacE M).1 hf _ _ ⟨hat u h.1, hat u' h.2.1, fun w => ?_⟩, map_smul]
    rw [Matrix.map_mul, Matrix.map_mul, h.2.2 w, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (hk w).eq]
    simp only [Matrix.mul_assoc]
  · obtain ⟨u, hu, e⟩ := exists_ph M (Module.finBasis ℝ _ i)
    rw [← e, dopL_ph, inter' hψ hs hg hA hu, ← dopL_ph]
    exact dopL_mem _ _ _ _

end PositivityTheory.ThKCT.So

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.TwoExp
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open Matrix (vecMulVec)

theorem split_triv {A I J : Type} {e : I → A → ℂ} {c : I → ℂ} {j : J → I} (hj : Function.Injective j) (h1 : ∀ k a, e (j k) a = 1)
    {a : A} {S : ℂ} (h : HasSum (fun i => c i * e i a) S) :
    HasSum (fun i : ↥(Set.range j)ᶜ => c i * e i a) (S - ∑' k, c (j k)) := by
  have h2 := h.summable.tsum_subtype_add_tsum_subtype_compl (Set.range j)
  rw [tsum_range (fun i => c i * e i a) hj, h.tsum_eq] at h2
  simp only [h1, mul_one] at h2
  rw [← h2, add_sub_cancel_left]
  exact (h.summable.subtype _).hasSum

theorem triv_part {A I₁ I₂ J₁ J₂ : Type} [AddCommGroup A] {e₁ : I₁ → A → ℂ} {e₂ : I₂ → A → ℂ} {c₁ : I₁ → ℂ} {c₂ : I₂ → ℂ}
    {j₁ : J₁ → I₁} {j₂ : J₂ → I₂} (i₁ : Function.Injective j₁) (i₂ : Function.Injective j₂)
    (m₁ : ∀ i a b, e₁ i (a + b) = e₁ i a * e₁ i b) (m₂ : ∀ i a b, e₂ i (a + b) = e₂ i a * e₂ i b)
    (l₁ : ∀ i a, ‖e₁ i a‖ ≤ 1) (l₂ : ∀ i a, ‖e₂ i a‖ ≤ 1) (t₁ : ∀ k a, e₁ (j₁ k) a = 1) (t₂ : ∀ k a, e₂ (j₂ k) a = 1)
    (n₁ : ∀ i ∉ Set.range j₁, ∃ a, e₁ i a ≠ 1) (n₂ : ∀ i ∉ Set.range j₂, ∃ a, e₂ i a ≠ 1) (s₁ : Summable c₁) (s₂ : Summable c₂)
    {S : A → ℂ} (h₁ : ∀ a, HasSum (fun i => c₁ i * e₁ i a) (S a)) (h₂ : ∀ a, HasSum (fun i => c₂ i * e₂ i a) (S a)) :
    ∑' k, c₁ (j₁ k) = ∑' k, c₂ (j₂ k) := by
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.ThetaInj.charSeries_coeff_eq_zero (A := A) (I := Unit ⊕ (↥(Set.range j₁)ᶜ ⊕ ↥(Set.range j₂)ᶜ))
    (Sum.elim (fun _ _ => 1) (Sum.elim (fun i => e₁ i) fun i => e₂ i))
    (Sum.elim (fun _ => ∑' k, c₁ (j₁ k) - ∑' k, c₂ (j₂ k)) (Sum.elim (fun i => c₁ i) fun i => -c₂ i)) (Sum.inl ())
    ?_ ?_ (fun _ => rfl) ?_ (Summable.norm ?_) fun a => ?_)
  · rintro (_ | i | i) a b
    exacts [(one_mul _).symm, m₁ i a b, m₂ i a b]
  · rintro (_ | i | i) a
    exacts [norm_one.le, l₁ i a, l₂ i a]
  · rintro (_ | i | i) h
    exacts [absurd rfl h, n₁ i i.2, n₂ i i.2]
  · exact Summable.sum _ Summable.of_finite (Summable.sum _ (s₁.subtype _) (s₂.subtype _).neg)
  · refine HasSum.tsum_eq ?_
    have k₂ : HasSum (fun i : ↥(Set.range j₂)ᶜ => -c₂ i * e₂ i a) (-(S a - ∑' k, c₂ (j₂ k))) := by
      simpa only [neg_mul] using (split_triv i₂ t₂ (h₂ a)).neg
    rw [show (0 : ℂ) = (∑' k, c₁ (j₁ k) - ∑' k, c₂ (j₂ k)) * 1 + ((S a - ∑' k, c₁ (j₁ k)) + -(S a - ∑' k, c₂ (j₂ k))) by ring]
    refine HasSum.sum (hasSum_unique _) (HasSum.sum ?_ ?_)
    · exact split_triv i₁ t₁ (h₁ a)
    · exact k₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {H : Plane E n n₁} {H' : Plane E d d₁} {ε ε' : ℤ}

theorem PG.eps_ne (h : PG σ X X₁ H ε) : (ε : E) ≠ 0 := left_ne_zero_of_mul_eq_one h.rat.ee

theorem PG.nd_low' (h : PG σ X X₁ H ε) (u) (hu : ∀ z, bf σ.toRingHom X.J (H.ι *ᵥ u) (H.ι *ᵥ z) = 0) : u = 0 :=
  h.nd_low u fun z => by rw [h.rat.symm, hu, map_zero, mul_zero]

theorem PG.line (h : PG σ X X₁ H ε) (a) (h1 : bf σ.toRingHom X.J a H.x = 0) (h2 : ∀ z, bf σ.toRingHom X.J a (H.ι *ᵥ z) = 0) :
    ∃ ξ : E, ξ • H.x = a := by
  obtain ⟨s, t, z, rfl⟩ := h.rat.span a
  simp only [bf_add_l, bf_smul_l, h.rat.xx, h.rat.ix, h.rat.yx, h.rat.xi, h.rat.yi, mul_zero, zero_add, add_zero] at h1 h2
  refine ⟨s, ?_⟩
  rw [h.nd_low' z h2, (mul_eq_zero.1 h1).resolve_right h.eps_ne]
  simp

theorem PG.x_ne (h : PG σ X X₁ H ε) : H.x ≠ 0 := fun h0 => by
  have := h.rat.xy
  rw [h0] at this
  simp [bf] at this


variable (H H') in
def capAB : Submodule (AE F E) (Ten F E n d) where
  carrier := sumA H H' ∩ sumB H H'
  zero_mem' := ⟨⟨0, 0, by simp [vv0]⟩, ⟨0, 0, by simp [vv0]⟩⟩
  add_mem' := by
    rintro a b ⟨⟨y, z, e⟩, ⟨z', y', e'⟩⟩ ⟨⟨y₁, z₁, e₁⟩, ⟨z₁', y₁', e₁'⟩⟩
    refine ⟨⟨y + y₁, z + z₁, ?_⟩, ⟨z' + z₁', y' + y₁', ?_⟩⟩
    · rw [e, e₁, Matrix.add_vecMulVec, Matrix.mulVec_add, Matrix.vecMulVec_add]; abel
    · rw [e', e₁', Matrix.mulVec_add, Matrix.add_vecMulVec, Matrix.vecMulVec_add]; abel
  smul_mem' := by
    rintro c a ⟨⟨y, z, e⟩, ⟨z', y', e'⟩⟩
    refine ⟨⟨c • y, c • z, ?_⟩, ⟨c • z', c • y', ?_⟩⟩
    · rw [e, Matrix.smul_vecMulVec, Matrix.mulVec_smul, Matrix.vecMulVec_smul, smul_add]
    · rw [e', Matrix.mulVec_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_add]

theorem cap_xx : incM F (vecMulVec H.x H'.x) ∈ capAB (F := F) H H' := by
  rw [incM_vv]
  exact ⟨⟨incV F H.x, 0, by simp [vv0]⟩, ⟨incV F H'.x, 0, by simp [vv0]⟩⟩

theorem cap_ix (u) : incM F (vecMulVec (H.ι *ᵥ u) H'.x) ∈ capAB (F := F) H H' := by
  rw [incM_vv, ← inc_mulVec]
  exact ⟨⟨incM F H.ι *ᵥ incV F u, 0, by simp [vv0]⟩, ⟨0, incV F u, by simp [vv0]⟩⟩

theorem cap_xi (u) : incM F (vecMulVec H.x (H'.ι *ᵥ u)) ∈ capAB (F := F) H H' := by
  rw [incM_vv, ← inc_mulVec]
  exact ⟨⟨0, incV F u, by simp [vv0]⟩, ⟨incM F H'.ι *ᵥ incV F u, 0, by simp [vv0]⟩⟩

theorem incM_smul (l : E) (v : Matrix (Fin n) (Fin d) E) : incM F (l • v) = inclR (F := F) (AF F) l • incM F v := by
  ext i j
  simp [incM]

theorem exists_ne (M : Model σ X W) (hψ : IsStd B.ψ) (cc : ∀ a, σ (σ a) = a) {x v : Matrix (Fin n) (Fin d) E}
    (hv : incM F v ∈ capAB (F := F) H H') (h : hTens σ X.J W.J x v ≠ 0) :
    ∃ a : capAB (F := F) H H', B.ψ (sy σ X W (incM F x) a.1) ≠ 1 := by
  obtain ⟨l, hl⟩ : ∃ l, Algebra.trace F E (-hTens σ X.J W.J x v * l) ≠ 0 := by
    by_contra h0
    push Not at h0
    exact h (neg_eq_zero.1 ((traceForm_nondegenerate F E).1 _ fun a => h0 a))
  obtain ⟨b, hb⟩ := DFunLike.ne_iff.1 (std_ne_one hψ)
  refine ⟨⟨(b * algebraMap F (AF F) (Algebra.trace F E (-hTens σ X.J W.J x v * l))⁻¹) • incM F (σ l • v), ?_⟩, ?_⟩
  · rw [← algebraMap_smul (AE F E), incM_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hv)
  · have e := sy_inc (σ := σ) (X := X) (W := W) x (σ l • v)
    rw [hT_smul_r, cc, mul_comm, ← neg_mul] at e
    change B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _) ≠ 1
    rw [form_eq M.co, map_smul, ← form_eq M.co, show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _ from e,
      smul_eq_mul, mul_assoc, ← map_mul, inv_mul_cancel₀ hl, map_one, mul_one]
    simpa using hb

theorem twoExp_of (hE : ThetaExp) : TwoExp := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' hB hX hW hM hM₀ eA eB hA hBv
  have hψ := hB.std
  have p := pg_herm hB hH hX
  have p' := pg_skew hB hH' hW
  have hA' := isEv_sumA hψ p' hA
  have hB' := isEv_sumB hψ p hBv
  obtain ⟨C, hC, h1⟩ := (polA p p').exp hE hB hM hM₀ hA'
  obtain ⟨C', hC', h2⟩ := (polB p p').exp hE hB hM hM₀ hB'
  have eA' : ∀ ξ : E, vA H.y H'.y H'.ι (ξ • H.x, 0) = ξ • vecMulVec H.x H'.y := fun ξ => by
    simp [vv0, vA_apply, Matrix.smul_vecMulVec]
  have eB' : ∀ ξ : E, vB H.y H'.y H.ι (ξ • H'.x, 0) = ξ • vecMulVec H.y H'.x := fun ξ => by
    simp [vB_apply, Matrix.vecMulVec_smul]
  have iA : Function.Injective fun ξ : E => ((ξ • H.x, 0) : (Fin n → E) × (Fin d₁ → E)) := fun a b e =>
    smul_left_injective E p.x_ne (congrArg Prod.fst e)
  have iB : Function.Injective fun ξ : E => ((ξ • H'.x, 0) : (Fin d → E) × (Fin n₁ → E)) := fun a b e =>
    smul_left_injective E p'.x_ne (congrArg Prod.fst e)
  have hm : ∀ x a b, B.ψ (sy σ X W x (a + b)) = B.ψ (sy σ X W x a) * B.ψ (sy σ X W x b) := fun x a b => by
    rw [← AddChar.map_add_eq_mul]
    exact congrArg B.ψ ((formL M.co x).map_add a b)
  refine ⟨C⁻¹ * C', mul_ne_zero (inv_ne_zero hC) hC', fun Ψ hΨ => ⟨?_, ?_, ?_⟩⟩
  · simpa only [Function.comp_def, eA'] using ((summable_mul_left_iff hC).1 (h1 Ψ hΨ).summable).comp_injective iA
  · simpa only [Function.comp_def, eB'] using ((summable_mul_left_iff hC').1 (h2 Ψ hΨ).summable).comp_injective iB
  have key := triv_part (A := capAB (F := F) H H') (e₁ := fun t a => B.ψ (sy σ X W (incM F (vA H.y H'.y H'.ι t)) a.1))
    (e₂ := fun t a => B.ψ (sy σ X W (incM F (vB H.y H'.y H.ι t)) a.1)) iA iB (fun t a b => hm _ _ _) (fun t a b => hm _ _ _)
    (fun _ _ => (std_norm hψ _).le) (fun _ _ => (std_norm hψ _).le) ?_ ?_ ?_ ?_ (h1 Ψ hΨ).summable (h2 Ψ hΨ).summable
    (S := fun a => thetaSum F (M.co.rho B.ψ a.1 Ψ)) (fun a => ?_) (fun a => ?_)
  · simp only [eA', eB', tsum_mul_left] at key
    rw [mul_assoc, ← key, inv_mul_cancel_left₀ hC]
  · rintro ξ ⟨_, -, y, z, rfl⟩
    rw [eA', sy_of_hT, AddChar.map_zero_eq_one]
    rw [incM_smul, incM_vv, hT_smul_l, hT_add_r, hT_vv, hT_vv, p.ad.xx, p.ad.xi]
    simp
  · rintro ξ ⟨_, ⟨y, z, rfl⟩, -⟩
    rw [eB', sy_of_hT, AddChar.map_zero_eq_one]
    rw [incM_smul, incM_vv, hT_smul_l, hT_add_r, hT_vv, hT_vv, p'.ad.xx, p'.ad.xi]
    simp
  · rintro ⟨a, b⟩ hn
    by_contra h0
    have k : ∀ v, incM F v ∈ capAB (F := F) H H' → hTens σ X.J W.J (vA H.y H'.y H'.ι (a, b)) v = 0 := fun v hv => by
      by_contra h3
      exact h0 (exists_ne M hψ p.rat.cc hv h3)
    have k1 := k _ cap_xx
    have k2 := fun u => k _ (cap_ix u)
    have k3 := fun u => k _ (cap_xi u)
    simp only [vA_apply, hT_add_l, hT_vv, p'.rat.yx, p'.rat.ix, p'.rat.yi, p.rat.yx, p.rat.yi, mul_zero, add_zero, zero_add,
      mul_eq_zero, p.eps_ne, p'.eps_ne, or_false, false_or] at k1 k2 k3
    obtain ⟨ξ, rfl⟩ := p.line a k1 k2
    exact hn ⟨ξ, by rw [p'.nd_low' b k3]⟩
  · rintro ⟨a, b⟩ hn
    by_contra h0
    have k : ∀ v, incM F v ∈ capAB (F := F) H H' → hTens σ X.J W.J (vB H.y H'.y H.ι (a, b)) v = 0 := fun v hv => by
      by_contra h3
      exact h0 (exists_ne M hψ p.rat.cc hv h3)
    have k1 := k _ cap_xx
    have k2 := fun u => k _ (cap_xi u)
    have k3 := fun u => k _ (cap_ix u)
    simp only [vB_apply, hT_add_l, hT_vv, p'.rat.yx, p.rat.ix, p'.rat.yi, p.rat.yx, p.rat.yi, zero_mul, add_zero, zero_add,
      mul_eq_zero, p.eps_ne, p'.eps_ne, or_false, false_or] at k1 k2 k3
    obtain ⟨ξ, rfl⟩ := p'.line a k1 k2
    exact hn ⟨ξ, by rw [p.nd_low' b k3]⟩
  · convert h1 _ (rho_mem M hψ a.1 hΨ) using 2 with t
    rw [rho_comm, map_smul, hA'.inv _ a.2.1 _ (rho_mem M hψ _ hΨ), thetaSum_smul]
    ring
  · convert h2 _ (rho_mem M hψ a.1 hΨ) using 2 with t
    rw [rho_comm, map_smul, hB'.inv _ a.2.2 _ (rho_mem M hψ _ hΨ), thetaSum_smul]
    ring

end PositivityTheory.ThKCT.Ker
end
end

