module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host nonZeroDivisors

namespace GlobalTheory.HeckeProduct

section Comp
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion L)

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion L)

theorem localIdele_fst (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) w = x
  convert Pi.mulSingle_eq_same w (x : w.Completion)

theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) u = 1
  convert Pi.mulSingle_eq_of_ne h (x : w.Completion)

end Comp

section Parts
variable (F : Type) [Field F] [NumberField F]

def infPart : Ideles F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def finPart : Ideles F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

variable {F}

theorem infDiag_parts (k : Fˣ) : infPart F (infDiag k) = infPart F (diagUnits F k) ∧ finPart F (infDiag k) = 1 := by
  classical
  constructor
  · apply Units.ext
    funext w
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]
    have e : (∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) :
        InfiniteAdeleRing F)) w = ∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) :
          (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w := Finset.prod_apply _ _ _
    rw [e, Finset.prod_eq_single w]
    · exact infIdele_fst_self F w _
    · intro u _ hu
      exact infIdele_fst_ne F u w (Ne.symm hu) _
    · simp
  · rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => Units.ext rfl

end Parts

section Product

variable {F : Type} [Field F] [NumberField F]


open Classical in
def cut (a : FiniteAdeleRing (𝓞 F) F) (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then a v else 1, by
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    have h' : w ∉ T := h
    simp only [h', if_false]
    exact one_mem _⟩

theorem tendsto_cut (a : FiniteAdeleRing (𝓞 F) F) : Filter.Tendsto (cut a) Filter.atTop (nhds a) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem prod_local (k : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F) =
      (((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).1, cut ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).2 T) := by
  classical
  refine Prod.ext ?_ ?_
  · change ((infPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _
    have e : ∏ v ∈ T, infPart F (localIdele F v (atFin v k)) = 1 := Finset.prod_eq_one (fun v _ => Units.ext rfl)
    rw [map_mul, map_prod, (infDiag_parts k).1, e, mul_one]
    rfl
  · change ((finPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = _
    rw [map_mul, (infDiag_parts k).2, one_mul]
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; exact Subtype.ext (funext fun v => by simp [cut]; rfl)
    | insert u T hu ih =>
      rw [Finset.prod_insert hu, map_mul, Units.val_mul, ih]
      refine Subtype.ext (funext fun v => ?_)
      change ((localIdele F u (atFin u k) : Ideles F) : AdeleRing (𝓞 F) F).2 v * (if v ∈ T then _ else 1) =
        if v ∈ insert u T then _ else 1
      by_cases h : v = u
      · subst h
        rw [localIdele_snd_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]; rfl
      · rw [localIdele_snd_ne F u v h, one_mul]; simp [h]

theorem tendsto_prod_local (k : Fˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
      Filter.atTop (nhds (diagUnits F k)) := by
  have h : ∀ k : Fˣ, Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F))
      Filter.atTop (nhds ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F)) := fun k => by
    simp only [prod_local]
    exact tendsto_const_nhds.prodMk_nhds (tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h k).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h k⁻¹
  simp only [map_inv, Finset.prod_inv_distrib, ← mul_inv] at h2
  exact h2

theorem locK_unr (χ : HChar F) {v : HeightOneSpectrum (𝓞 F)} (h : χ.UnrAt v) (k : Fˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  have hu : IsUnitAt v (atFin v (k * (unif v ^ ordF v k)⁻¹)) := by
    have h2 := unif_spec v
    have hk : Valued.v ((atFin v k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = v.valuation F (k : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
    have h0 : v.valuation F (k : F) ≠ 0 := by simp
    unfold IsUnitAt IsUnifAt at *
    rw [map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, hk, ← WithZero.exp_zsmul, ordF]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 : χ.locK v (k * (unif v ^ ordF v k)⁻¹) = 1 := h _ hu
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

theorem finite_ordF (k : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordF v k ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (FiniteAdeleRing.unitEmbedding (𝓞 F) F k))
  refine h.subset fun v hv h0 => hv ?_
  have hk : Valued.v (((FiniteAdeleRing.unitEmbedding (𝓞 F) F k : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v) = v.valuation F (k : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
  rw [GlobalTheory.Idele.ord_vw, hk] at h0
  exact h0

theorem productRule (χ : HChar F) : χ.ProductRule := by
  classical
  intro S hS k
  have h1 := (χ.2.1.tendsto _).comp (tendsto_prod_local k)
  rw [χ.2.2 k] at h1
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1
  filter_upwards [Filter.eventually_ge_atTop (S ∪ (finite_ordF k).toFinset)] with T hT
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  change _ = χ.1 (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
  rw [map_mul, map_prod, mul_assoc, ← Finset.prod_sdiff hST, mul_comm (∏ v ∈ T \ S, _)]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl ?_)
  rw [finprod_cond_eq_prod_of_cond_iff (fun v => χ.val v ^ ordF v k) (p := fun v => v ∉ S) (t := T \ S)]
  · exact Finset.prod_congr rfl fun v hv => (locK_unr χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm
  · intro v hv
    rw [Finset.mem_sdiff]
    refine ⟨fun h => ⟨hT (Finset.mem_union_right _ ?_), h⟩, fun h => h.2⟩
    rw [Set.Finite.mem_toFinset]
    intro h0
    exact hv (by rw [h0, zpow_zero])

end Product

theorem hchar_productRule : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), χ.ProductRule :=
  fun _ _ _ χ => productRule χ

end GlobalTheory.HeckeProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdFNonnegOfIsInteger
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Chr.DetOrd

variable {L : Type} [Field L] [NumberField L]

theorem ordF_mul' (w : HeightOneSpectrum (𝓞 L)) (a b : Lˣ) : ordF w (a * b) = ordF w a + ordF w b := by
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hb : w.valuation L (b : L) ≠ 0 := by simp
  unfold ordF
  rw [Units.val_mul, map_mul, WithZero.log_mul ha hb]
  ring

theorem ordF_nonneg_of_isInteger (w : HeightOneSpectrum (𝓞 L)) (a : Lˣ)
    (h : IsLocalization.IsInteger (𝓞 L) (a : L)) : 0 ≤ ordF w a := by
  obtain ⟨r, hr⟩ := h
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hle : w.valuation L (a : L) ≤ 1 := by
    rw [← hr]; exact w.valuation_le_one r
  have := (WithZero.log_le_log ha one_ne_zero).2 hle
  unfold ordF
  simpa using this

theorem ordF_finite (a : Lˣ) : {w : HeightOneSpectrum (𝓞 L) | ordF w a ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 L) (a : L)).union
    (HeightOneSpectrum.Support.finite (𝓞 L) ((a⁻¹ : Lˣ) : L))).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hn
  apply hw
  have h0 : w.valuation L (a : L) ≠ 0 := by simp
  have h1 : w.valuation L (a : L) = 1 := by
    refine le_antisymm hn.1 ?_
    have h2 := hn.2
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
    exact (inv_le_one₀ (zero_lt_iff.2 h0)).1 h2
  simp [ordF, h1]

theorem isFractional_detSub {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (hM : M.FG) :
    IsFractional (𝓞 L)⁰ (detSub M) := by
  obtain ⟨a, ha, hint⟩ := Formalism.L2.LamCM.A2.exists_den M hM
  refine ⟨a ^ N, pow_mem ha N, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ N) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 L) L a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

theorem exists_bound {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) :
    ∃ d : Lˣ, ∀ w : HeightOneSpectrum (𝓞 L), ∀ k : Lˣ, (k : L) ∈ A → -ordF w d ≤ ordF w k := by
  obtain ⟨a, ha, hint⟩ := h
  have ha0 : algebraMap (𝓞 L) L a ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero ha
  refine ⟨Units.mk0 _ ha0, fun w k hk => ?_⟩
  have h1 := ordF_nonneg_of_isInteger w (Units.mk0 _ ha0 * k) (by
    have := hint _ hk
    rwa [Algebra.smul_def] at this)
  rw [ordF_mul'] at h1
  linarith

theorem isLeast_ordSub {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (w : HeightOneSpectrum (𝓞 L)) :
    IsLeast {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} (ordSub w A) := by
  obtain ⟨d, hd⟩ := exists_bound h
  have hb : BddBelow {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} :=
    ⟨-ordF w d, by rintro n ⟨k, hk, rfl⟩; exact hd w k hk⟩
  exact ⟨Int.csInf_mem ⟨_, k0, hk0, rfl⟩ hb, fun n hn => csInf_le hb hn⟩

theorem ordSub_finite {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A) :
    {w : HeightOneSpectrum (𝓞 L) | ordSub w A ≠ 0}.Finite := by
  obtain ⟨d, hd⟩ := exists_bound h
  refine ((ordF_finite d).union (ordF_finite k0)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
  apply hw
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  have h1 := hl ⟨k0, hk0, rfl⟩
  have h2 := hd w k hk
  omega

theorem det_of_mulVec {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (x : Fin N → Fin N → L) :
    (Matrix.of fun i => γ.mulVec (x i)).det = γ.det * (Matrix.of x).det := by
  have : (Matrix.of fun i => γ.mulVec (x i)) = Matrix.of x * γ.transpose := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, mul_comm]

theorem detSub_map {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (M : Submodule (𝓞 L) (Fin N → L)) :
    detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L))) =
      (detSub M).map (LinearMap.mulLeft (𝓞 L) γ.det) := by
  unfold detSub
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    choose x hx e using fun i => Submodule.mem_map.1 (hy i)
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    have : y = fun i => γ.mulVec (x i) := funext fun i => by
      rw [← e i]; simp
    rw [this, det_of_mulVec]
    rfl
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨fun i => γ.mulVec (x i), fun i => Submodule.mem_map.2 ⟨x i, hx i, by simp⟩, ?_⟩
    rw [det_of_mulVec]
    rfl

theorem ordSub_map_mul {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (u : Lˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ordSub w (A.map (LinearMap.mulLeft (𝓞 L) (u : L))) = ordF w u + ordSub w A := by
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  refine IsLeast.csInf_eq ⟨⟨u * k, Submodule.mem_map.2 ⟨k, hk, rfl⟩, by rw [ordF_mul', e]⟩, ?_⟩
  rintro n ⟨k', hk', rfl⟩
  obtain ⟨y, hy, ey⟩ := Submodule.mem_map.1 hk'
  have ey' : (u : L) * y = k' := ey
  have hy' : ((u⁻¹ * k' : Lˣ) : L) = y := by
    rw [Units.val_mul, ← ey', Units.inv_mul_cancel_left]
  have h1 := hl ⟨u⁻¹ * k', hy' ▸ hy, rfl⟩
  have h2 : ordF w k' = ordF w u + ordF w (u⁻¹ * k') := by
    rw [← ordF_mul', mul_inv_cancel_left]
  omega

end GlobalTheory.Mem.Chr.DetOrd

namespace GlobalTheory.Mem.Chr

open DetOrd


open Classical in
theorem ordSub_detSub_lattice :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Submodule (𝓞 L) (Fin N → L)), M.FG → Submodule.span L (M : Set (Fin N → L)) = ⊤ → {w | ordSub w (detSub M) ≠ 0}.Finite ∧ (∀ w, IsLeast {n | ∃ k : Lˣ, (k : L) ∈ detSub M ∧ ordF w k = n} (ordSub w (detSub M))) ∧ ∀ (γ : Matrix (Fin N) (Fin N) L) (u : Lˣ), γ.det = u → ∀ w, ordSub w (detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L)))) = ordF w u + ordSub w (detSub M) := by
  intro L _ _ N M hfg hsp
  have hf := isFractional_detSub M hfg
  obtain ⟨x, hx, hd⟩ := Formalism.L2.LamCM.A2.exists_det_ne M hsp
  have hk : ((Units.mk0 _ hd : Lˣ) : L) ∈ detSub M := det_mem_detSub x hx
  refine ⟨ordSub_finite hf _ hk, isLeast_ordSub hf _ hk, fun γ u hu w => ?_⟩
  have e := detSub_map γ M
  have hu' : γ.det = u := by convert hu
  rw [hu'] at e
  have := ordSub_map_mul hf _ hk u w
  rw [← e] at this
  convert this

end GlobalTheory.Mem.Chr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem conjPl_iff_comap (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ v.asIdeal = v'.asIdeal.comap (RingOfIntegers.mapRingEquiv c) := by
  constructor
  · intro h
    ext x
    have h1 : v'.valuation L (algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv c x)) =
        v.valuation L (algebraMap (𝓞 L) L x) := h (algebraMap (𝓞 L) L x)
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), h1]
  · intro h x
    exact (GlobalTheory.QNorm.valuation_of_eq_comap c v' v h x).symm

theorem conjPl_iff_mem (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ ∀ x y : 𝓞 L, (y : L) = c (x : L) → (x ∈ v.asIdeal ↔ y ∈ v'.asIdeal) := by
  rw [conjPl_iff_comap]
  constructor
  · intro h x y hxy
    have e : y = RingOfIntegers.mapRingEquiv c x := RingOfIntegers.ext hxy
    rw [h, Ideal.mem_comap, e]
  · intro h
    ext x
    exact h x (RingOfIntegers.mapRingEquiv c x) rfl

theorem existsUnique_conjPl (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : ∃! v', ConjPl c v v' := by
  set e : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv c with he
  refine ⟨v.comap (e.symm : 𝓞 L →+* 𝓞 L) e.symm.surjective, ?_, ?_⟩
  · show ConjPl c v _
    rw [conjPl_iff_comap]
    ext x
    change x ∈ v.asIdeal ↔ e.symm (e x) ∈ v.asIdeal
    rw [e.symm_apply_apply]
  · intro v' h
    rw [conjPl_iff_comap] at h
    ext x
    change x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal
    rw [h, Ideal.mem_comap, e.apply_symm_apply]

theorem under_eq_iff_conjPl {F : Type} [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L)
    (hr : Module.finrank F L = 2) (hc : c ≠ 1) (w w' : HeightOneSpectrum (𝓞 L)) :
    w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') := by
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := hr }
  have : IsGalois F L := inferInstance
  have hall : ∀ σ : L ≃ₐ[F] L, σ = 1 ∨ σ = c := by
    intro σ
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hr]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
    by_cases h : σ = 1
    · exact Or.inl h
    · exact Or.inr ((hy σ h).trans (hy c hc).symm)
  constructor
  · intro hu
    have := w.isPrime
    have := w'.isPrime
    have hu' : w'.asIdeal.under (𝓞 F) = w.asIdeal.under (𝓞 F) := congrArg HeightOneSpectrum.asIdeal hu
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F L (𝓞 L) (p := w.asIdeal.under (𝓞 F))
      (P₁ := w'.asIdeal) (P₂ := w.asIdeal) ⟨inferInstance, ⟨hu'.symm⟩⟩ ⟨inferInstance, ⟨rfl⟩⟩
    rcases hall σ with rfl | rfl
    · left
      ext x
      rw [← hσ, map_one, Ideal.mem_comap]
      rfl
    · right
      rw [conjPl_iff_mem]
      intro x y hxy
      have e : y = galRestrict (𝓞 F) F L (𝓞 L) σ x := by
        apply RingOfIntegers.ext
        rw [hxy]
        exact (algebraMap_galRestrict_apply (𝓞 F) σ x).symm
      rw [← hσ, Ideal.mem_comap, e]
  · rintro (rfl | h)
    · rfl
    · rw [conjPl_iff_mem] at h
      ext a
      exact (h (algebraMap (𝓞 F) (𝓞 L) a) (algebraMap (𝓞 F) (𝓞 L) a) (c.commutes (a : F)).symm).symm

end General


open Classical in
theorem conjPl_main : (∀ (L : Type) [Field L] [NumberField L] (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)), ∃! v', ConjPl c v v') ∧ (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' ↔ ConjPl H.conj.toRingEquiv w w') ∧ ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L), Module.finrank F L = 2 → c ≠ 1 → ∀ (w w' : HeightOneSpectrum (𝓞 L)), w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') :=
  ⟨fun _ _ _ c v => existsUnique_conjPl c v,
    fun _ H w w' => (conjPl_iff_mem H.conj.toRingEquiv w w').symm,
    fun _ _ _ _ _ _ _ c hr hc w w' => under_eq_iff_conjPl c hr hc w w'⟩

end GlobalTheory.Mem.Chr
end

