module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace ClassSumTranslate

section Generic

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)

theorem card_stab (γ : Γ) (y : G) (k : J) :
    Nat.card (Bridge.stab ι J (ι γ * y * k)) = Nat.card (Bridge.stab ι J y) := by
  refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun δ => ?_)
  rw [Bridge.mem_stab, Bridge.mem_stab]
  have e : (ι γ * y * k)⁻¹ * ι δ * (ι γ * y * k) =
      (k : G)⁻¹ * (y⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * y) * k := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right k.2, J.mul_mem_cancel_left (J.inv_mem k.2)]

theorem adInnerIndep : Bridge.AdInnerIndep ι ρ J χ := by
  intro hρ hχ I I' _ _ y y' hy hy' F hF F' hF'
  choose σ hσ using fun i => (hy' (y i)).exists
  have hinj : Function.Injective σ := by
    intro i j hij
    obtain ⟨γ, k, h1⟩ := hσ i
    obtain ⟨γ', k', h2⟩ := hσ j
    refine (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨γ * γ'⁻¹, k'⁻¹ * k, ?_⟩
    rw [h1, h2, hij]; simp [mul_assoc]
  have hsurj : Function.Surjective σ := by
    intro j
    obtain ⟨i, γ, k, h1⟩ := (hy (y' j)).exists
    obtain ⟨γ', k', h2⟩ := hσ i
    refine ⟨i, (hy' (y' j)).unique ⟨γ * γ', k' * k, ?_⟩ ⟨1, 1, by simp⟩⟩
    rw [h1, h2]; simp [mul_assoc]
  unfold Bridge.adInner
  refine Fintype.sum_bijective σ ⟨hinj, hsurj⟩ _ _ fun i => ?_
  obtain ⟨γ, k, h⟩ := hσ i
  rw [h, card_stab, hF γ _ k, hF' γ _ k, inner_smul_left, inner_smul_right, hρ, ← mul_assoc (starRingEnd ℂ _),
    Complex.conj_mul', hχ]
  simp

variable {J} in
theorem stab_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) (y : G) :
    Bridge.stab ι J (y * κ) = Bridge.stab ι J y := by
  ext δ
  rw [Bridge.mem_stab, Bridge.mem_stab, ← hκ (y⁻¹ * ι δ * y)]
  simp [mul_assoc]

variable {J} in
theorem isReps_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) {I : Type} {y : I → G}
    (hy : Bridge.IsReps ι J y) : Bridge.IsReps ι J fun i => y i * κ := by
  intro h
  refine (existsUnique_congr fun i => ?_).1 (hy (h * κ⁻¹))
  constructor
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨_, (hκ k).2 k.2⟩, ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at e
    rw [e]; simp [mul_assoc]
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨κ * k * κ⁻¹, (hκ _).1 (by simpa [mul_assoc] using k.2)⟩, ?_⟩
    rw [e]; simp [mul_assoc]

theorem translate (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (κ : l.Q) {F : G → W}
    (hF : F ∈ Bridge.AdForms ι ρ l.J l.χ) :
    (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) ∈ Bridge.AdForms ι ρ l.J l.χ ∧
      Bridge.adInner ι l.J y (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ))
        (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) = Bridge.adInner ι l.J y F F := by
  have hκ : ∀ k, (κ : G)⁻¹ * k * κ ∈ l.J ↔ k ∈ l.J := fun k =>
    ⟨fun h => by simpa [mul_assoc] using hn _ (l.Q.inv_mem κ.2) _ h, hn _ κ.2 _⟩
  constructor
  · intro γ h k
    have e := hF γ (h * κ) ⟨_, (hκ k).2 k.2⟩
    have e2 : l.χ ⟨_, (hκ k).2 k.2⟩ = l.χ k := by
      rw [← l.ch_J, ← l.ch_J]
      have : (⟨(κ : G)⁻¹ * k * κ, l.J_le ((hκ k).2 k.2)⟩ : l.Q) = κ⁻¹ * ⟨k, l.J_le k.2⟩ * κ := rfl
      simp only
      rw [this, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    rw [e2] at e
    simp only
    rw [map_smul, smul_comm, ← e]
    simp [mul_assoc]
  · rw [adInnerIndep ι ρ l.J l.χ hρ (fun k => by rw [← l.ch_J]; exact hch _) I I y _ hy
      (isReps_mul ι hκ hy) F hF F hF]
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stab_mul ι hκ, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _),
      Complex.conj_mul', norm_inv, hch]
    simp

theorem translate_model (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (M : Links.HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ l.J l.χ) (Bridge.adInner ι l.J y)) (κ : l.Q) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = ((l.ch κ : ℂˣ) : ℂ)⁻¹ • M.e x (h * κ)) ∧ ‖x'‖ = ‖x‖ := by
  have hx : M.e x ∈ Bridge.AdForms ι ρ l.J l.χ := by
    rw [← hM.2.1]; exact ⟨x, rfl⟩
  obtain ⟨h1, h2⟩ := translate ι ρ l hρ hn hch hy κ hx
  rw [← hM.2.1] at h1
  obtain ⟨x', hx'⟩ := h1
  refine ⟨x', fun h => congrFun hx' h, ?_⟩
  have h3 : inner ℂ x' x' = inner ℂ x x := by
    rw [hM.2.2, hM.2.2, hx']; exact h2
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h3]

end Generic

theorem norm_char {M : Type} [Group M] [Finite M] (c : M →* ℂˣ) (x : M) : ‖(c x : ℂ)‖ = 1 := by
  have h : IsOfFinOrder (((Units.coeHom ℂ).comp c) x) := MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite x)
  exact h.norm_eq_one

variable {D : D7}

theorem norm_levFn (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Lev.EAf D)) : ‖((levFn β (flagL L) x : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) x) = 1 := subgroupCharExtension_one_apply _ _
  have hf : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => by
    first | infer_instance | exact Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  unfold levFn
  rw [h2, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod, norm_prod,
    Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_char _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_char _ _

theorem lev_conj (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {q k : GL (Fin V.rank) (Lev.EAf D)} (hq : q ∈ lev D.sp.cm V.gram β (flagL L))
    (hk : k ∈ lev D.sp.cm V.gram β (flag1L L)) : q⁻¹ * k * q ∈ lev D.sp.cm V.gram β (flag1L L) := by
  have hq' : q ∈ parLev D.sp.cm V.gram β L := hq.1
  have hk' : k ∈ parLev D.sp.cm V.gram β L := hk.1
  have hk2 : rTup β L k ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2
  have h1 : q⁻¹ * k * q ∈ parLev D.sp.cm V.gram β L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq'
  have h2 : rTup β L (q⁻¹ * k * q) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := by
    rw [Subgroup.mem_bot] at hk2 ⊢
    rw [rTup_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq', rTup_mul (Subgroup.inv_mem _ hq') hk',
      rTup_inv hq', hk2, mul_one, inv_mul_cancel]
  exact ⟨h1, h2⟩

theorem comap_conj {G H : Type} [Group G] [Group H] (f : G →* H) {Q J : Subgroup H}
    (h : ∀ q ∈ Q, ∀ k ∈ J, q⁻¹ * k * q ∈ J) : ∀ q ∈ Q.comap f, ∀ k ∈ J.comap f, q⁻¹ * k * q ∈ J.comap f := by
  intro q hq k hk
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact h _ hq _ hk

theorem levEnv_normal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ q ∈ (levEnv V β L).Q, ∀ k ∈ (levEnv V β L).J, q⁻¹ * k * q ∈ (levEnv V β L).J :=
  comap_conj (finHom V).range.subtype (comap_conj (Formalism.UG.bc (swapAE D)) fun _ hq _ hk => lev_conj V β L hq hk)

theorem model (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V) (hc : c.Is)
    (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = (levChi V β (flagL L) κ)⁻¹ • M.e x (h * (finHom V).rangeRestrict κ)) ∧
      ‖x'‖ = ‖x‖ := by
  have hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q := ⟨hκ.2.1, Subgroup.mem_top _⟩
  exact translate_model (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L)
    (fun γ u v => hc.2.1 _ u v) (levEnv_normal V β L) (fun q => norm_levFn V β L _) hy M hM ⟨_, hq⟩ x

end ClassSumTranslate

theorem translate_unitary_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HV → R.models_cV → ∀ i t g0 κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → ∀ y : (R.HV i t).H, ∃ y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) ∧ ‖y'‖ = ‖y‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hH hc i t g0 κ hκ y
  exact ClassSumTranslate.model _ _ _ _ (hc i) _ _ (R.B.L i t).pres.reps (hH i t) g0 κ hκ y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryBorelPreservesMixedModelLatticeLowerBlock
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.MixStab

variable {L : Type} [Field L]

theorem sum_hi {M : Type} [AddCommMonoid M] (N : ℕ) (f : Fin N → M)
    (hf : ∀ i : Fin N, i.1 < N - N / 2 → f i = 0) : ∑ i, f i = ∑ k, f (hi N k) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := hi N) (f := f)]
  · symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hni => hf i ?_
    by_contra hc
    have := i.isLt
    exact hni (Finset.mem_image.2 ⟨⟨i.1 - (N - N / 2), by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [hi]; omega)⟩)
  · intro x _ y _ hxy
    have := congrArg Fin.val hxy
    simp only [hi] at this
    exact Fin.ext (by omega)

theorem embLow_hi {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (k : Fin (n' / 2)) (l : Fin (n / 2)) :
    embLow n' n z (hi n' k) (hi n l) = z k l := by
  rw [embLow, dite_eq_left ⟨by simp [hi], by simp [hi]⟩]
  congr 1 <;> ext <;> simp [hi]

theorem embLow_eq_zero {n' n : ℕ} (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : r.1 < n' - n' / 2 ∨ c.1 < n - n / 2) : embLow n' n z r c = 0 := by
  rw [embLow, dite_eq_right (by omega)]

theorem mul_embLow_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n) :
    (A * embLow n' n z * B) r c = ∑ l, (∑ k, A r (hi n' k) * z k l) * B (hi n l) c := by
  rw [Matrix.mul_apply, sum_hi n]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, sum_hi n']
    · simp only [embLow_hi]
    · intro i hi'
      rw [embLow_eq_zero z i _ (Or.inl hi'), mul_zero]
  · intro j hj
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro i _
    rw [embLow_eq_zero z i j (Or.inr hj), mul_zero]

theorem lowBlock_mul_apply {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin (n' / 2)) (c : Fin (n / 2)) :
    (lowBlock A * z * lowBlock B) r c = ∑ l, (∑ k, A (hi n' r) (hi n' k) * z k l) * B (hi n l) (hi n c) := by
  simp only [Matrix.mul_apply, lowBlock, Matrix.submatrix_apply]

theorem exists_hi {N : ℕ} (r : Fin N) (hr : N - N / 2 ≤ r.1) : ∃ k, r = hi N k :=
  ⟨⟨r.1 - (N - N / 2), by have := r.isLt; omega⟩, Fin.ext (by simp only [hi]; omega)⟩

theorem mul_embLow_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (B : Matrix (Fin n) (Fin n) L)
    (hB : ∀ i j : Fin n, j < i → B i j = 0) (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L) (r : Fin n') (c : Fin n)
    (h : n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2) :
    (A * embLow n' n z * B) r c = embLow n' n (lowBlock A * z * lowBlock B) r c := by
  by_cases hc : c.1 < n - n / 2
  · rw [embLow_eq_zero _ r c (Or.inr hc), mul_embLow_mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hB (hi n l) c (Fin.lt_def.2 (by simp only [hi]; omega)), mul_zero]
  · have hr : n' - n' / 2 ≤ r.1 := by omega
    obtain ⟨r', rfl⟩ := exists_hi r hr
    obtain ⟨c', rfl⟩ := exists_hi c (by omega)
    rw [mul_embLow_mul_apply, embLow_hi, lowBlock_mul_apply]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_mixLat_iff {n' n : ℕ} (x : Matrix (Fin n') (Fin n) L) : x ∈ mixLat L n' n ↔
    ∀ r c, (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧
      (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) := Iff.rfl

theorem borel_mid_int {σ : L →+* L} {N : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {b : GU σ N}
    (hb : IsBorelU b) (i : Fin N) (hi' : i.rev = i) : b.1.1 i i ∈ intL L := by
  have h := P.fSatake_unit_diag hb i
  rw [hi'] at h
  have h2 := congrArg Valued.v h
  rw [map_mul, hv, map_one] at h2
  rw [mem_intL]
  by_contra hc
  rw [not_le] at hc
  have : (1 : WithZero (Multiplicative ℤ)) < Valued.v (b.1.1 i i) * Valued.v (b.1.1 i i) := one_lt_mul'' hc hc
  rw [h2] at this
  exact lt_irrefl _ this

theorem row_mul_eq {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) (hA : ∀ i j : Fin n', j < i → A i j = 0)
    (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) (r : Fin n') (hr : n' / 2 ≤ r.1) (j : Fin n) :
    (A * a) r j = A r r * a r j := by
  rw [mem_mixLat_iff] at ha
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · intro i _ hir
    rcases lt_or_gt_of_ne hir with h1 | h1
    · rw [hA r i h1, zero_mul]
    · rw [(ha i j).1 (Or.inl (by have := Fin.lt_def.1 h1; omega)), mul_zero]
  · simp

theorem borel_mul_mem {σ : L →+* L} {n' n : ℕ} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ n} {h : GU σ n'}
    (hg : IsBorelU g) (hh : IsBorelU h) (a : Matrix (Fin n') (Fin n) L) (ha : a ∈ mixLat L n' n) :
    (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n := by
  have ha' := (mem_mixLat_iff a).1 ha
  rw [mem_mixLat_iff]
  intro r c
  constructor
  · intro hrc
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [row_mul_eq _ hh a ha r (by omega)]
    rcases hrc with hr | ⟨hr, hc⟩
    · rw [(ha' r j).1 (Or.inl hr), mul_zero, zero_mul]
    · by_cases hjc : j.1 ≤ c.1
      · rw [(ha' r j).1 (Or.inr ⟨hr, by omega⟩), mul_zero, zero_mul]
      · rw [hg j c (Fin.lt_def.2 (by omega)), mul_zero]
  · intro hr hc
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · rw [row_mul_eq _ hh a ha r hr]
      by_cases hz : a r c = 0
      · rw [hz, mul_zero, zero_mul]; exact zero_mem _
      · have h1 : ¬ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2) := fun e => hz ((ha' r c).1 e)
        have hrr : r.rev = r := Fin.ext (by rw [Fin.val_rev]; omega)
        have hcc : c.rev = c := Fin.ext (by rw [Fin.val_rev]; omega)
        exact mul_mem (mul_mem (borel_mid_int hv hh r hrr) ((ha' r c).2 hr hc)) (borel_mid_int hv hg c hcc)
    · intro j _ hjc
      rcases lt_or_gt_of_ne hjc with h1 | h1
      · rw [row_mul_eq _ hh a ha r hr, (ha' r j).1 (Or.inr ⟨hr, by have := Fin.lt_def.1 h1; omega⟩), mul_zero, zero_mul]
      · rw [hg j c h1, mul_zero]
    · simp

end GlobalTheory.SphTheta.MixStab

namespace GlobalTheory.SphTheta


open MixStab in
theorem borel_mixLat_lowBlock : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ a : Matrix (Fin n') (Fin n) L, a ∈ mixLat L n' n → (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ∃ a ∈ mixLat L n' n, (∀ (r : Fin n') (c : Fin n), c.1 < n - n / 2 → a r c = 0) ∧ (h.1.1 * embLow n' n z * g.1.1 : Matrix (Fin n') (Fin n) L) = a + embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1) := by
  intro L _ _ ϖ σ q hU n n' g h hg hh
  refine ⟨fun a ha => borel_mul_mem hU.2.1 hg hh a ha, fun z => ?_⟩
  have key : ∀ (r : Fin n') (c : Fin n), n' - n' / 2 ≤ r.1 ∨ c.1 < n - n / 2 →
      (h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1)) r c = 0 := fun r c e => by
    rw [Matrix.sub_apply, sub_eq_zero]
    exact mul_embLow_mul_eq _ _ hg _ r c e
  refine ⟨h.1.1 * embLow n' n z * g.1.1 - embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1), ?_,
    fun r c hc => key r c (Or.inr hc), (sub_add_cancel _ _).symm⟩
  rw [mem_mixLat_iff]
  intro r c
  refine ⟨fun e => key r c (by omega), fun _ hc => ?_⟩
  rw [key r c (Or.inr hc)]
  exact zero_mem _

end GlobalTheory.SphTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperTriangularUnitaryLowerHalfBlockTriangular
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.LowBlocks

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_congr_v {x y : L} (h : Valued.v x = Valued.v y) : Formalism.UG.ordL x = Formalism.UG.ordL y := by
  unfold Formalism.UG.ordL
  by_cases hx : Valued.v x = 0
  · have hy : Valued.v y = 0 := h ▸ hx
    rw [dite_eq_left hx, dite_eq_left hy]
  · have hy : Valued.v y ≠ 0 := h ▸ hx
    rw [dite_eq_right hx, dite_eq_right hy]
    congr 2
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_unzero, h]

theorem ordL_one_eq : Formalism.UG.ordL (1 : L) = 0 :=
  Formalism.UG.P.fIwasawa_ordL_unit 1 1 (by simp) (by simp) (by simp)

theorem ordL_of_mul_eq_one {x y : L} (h : x * y = 1) : Formalism.UG.ordL y = - Formalism.UG.ordL x := by
  have hx : x ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hy : y ≠ 0 := right_ne_zero_of_mul_eq_one h
  have := Formalism.UG.P.fIwasawa_ordL_mul x y hx hy
  rw [h, ordL_one_eq] at this
  omega

variable {σ : L →+* L} {n : ℕ}

theorem ordL_rev_diag (hv : ∀ x, Valued.v (σ x) = Valued.v x) {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    Formalism.UG.ordL (b.1.1 i.rev i.rev) = - Formalism.UG.ordL (b.1.1 i i) := by
  rw [ordL_of_mul_eq_one (Formalism.UG.P.fSatake_unit_diag hb i), ordL_congr_v (hv _)]

theorem diag_ne_zero {b : GU σ n} (hb : IsBorelU b) (i : Fin n) : b.1.1 i i ≠ 0 := fun h0 => by
  have := Formalism.UG.P.fSatake_unit_diag hb i
  rw [show (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 0 from h0, map_zero, zero_mul] at this
  exact zero_ne_one this

theorem lowBlock_tri {M : Matrix (Fin n) (Fin n) L} (hM : ∀ i j : Fin n, j < i → M i j = 0) :
    (lowBlock M).BlockTriangular id := fun i j hij => by
  apply hM
  rw [Fin.lt_def] at hij ⊢
  simp only [hi, id] at *
  omega

theorem hi_eq_rev_lo (r : Fin (n / 2)) : hi n r = (lo n r.rev).rev := by
  ext; simp only [hi, lo, Fin.val_rev]; omega

end GlobalTheory.SphTheta.LowBlocks


open GlobalTheory.SphTheta.LowBlocks in
theorem GlobalTheory.SphTheta.lowBlocks_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (hn : n ≤ n'), (∀ g : GU σ n, IsBorelU g → ∃ U : GL (Fin (n / 2)) L, U.1 = lowBlock g.1.1 ∧ U.1.BlockTriangular id ∧ ∀ r, ordL (U.1 r r) = -ordL (g.1.1 (lo n r.rev) (lo n r.rev))) ∧ ∀ h : GU σ n', IsBorelU h → ∃ V : GL (Fin (n / 2)) L, V.1.BlockTriangular id ∧ (∀ r : Fin (n / 2), ordL (V.1 r.rev r.rev) = ordL (h.1.1 (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩) (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩))) ∧ ∀ t : Matrix (Fin (n / 2)) (Fin (n / 2)) L, lowBlock (h⁻¹).1.1 * (Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0) = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then (V.1 * t) ⟨r.1, e⟩ c else 0 := by
  intro L _ _ ϖ σ q hU n n' hn
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  refine ⟨fun g hg => ?_, fun h hh => ?_⟩
  · have htri : (lowBlock g.1.1).BlockTriangular id := lowBlock_tri hg
    have hdet : (lowBlock g.1.1).det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]
      intro r _
      exact diag_ne_zero hg _
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, htri, fun r => ?_⟩
    show Formalism.UG.ordL (g.1.1 (hi n r) (hi n r)) = _
    rw [hi_eq_rev_lo, ordL_rev_diag hv hg]
  · have hle : n / 2 ≤ n' / 2 := Nat.div_le_div_right hn
    have hb' : IsBorelU h⁻¹ := Formalism.UG.P.fSatake_borel_inv hh
    set W := lowBlock (h⁻¹).1.1 with hW
    have hWt : W.BlockTriangular id := lowBlock_tri hb'
    set V0 : Matrix (Fin (n / 2)) (Fin (n / 2)) L := W.submatrix (Fin.castLE hle) (Fin.castLE hle) with hV0
    have htri : V0.BlockTriangular id := fun i j hij => hWt (by rw [Fin.lt_def] at hij ⊢; exact hij)
    have hdet : V0.det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]
      intro r _
      exact diag_ne_zero hb' _
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, htri, fun r => ?_, fun t => ?_⟩
    · show Formalism.UG.ordL ((h⁻¹).1.1 (hi n' (Fin.castLE hle r.rev)) (hi n' (Fin.castLE hle r.rev))) = _
      have e : hi n' (Fin.castLE hle r.rev) = (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev := by
        ext; simp only [hi, lo, Fin.val_rev, Fin.coe_castLE]; omega
      rw [e]
      have a := ordL_of_mul_eq_one (Formalism.UG.P.fSatake_borel_diag_inv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev)
      have b := ordL_rev_diag hv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩)
      change Formalism.UG.ordL (h.1.1 _ _) = - Formalism.UG.ordL ((h⁻¹).1.1 _ _) at a
      linarith
    · ext r c
      simp only [Matrix.mul_apply, Matrix.of_apply]
      split_ifs with hr
      · have hr' : (Fin.castLE hle ⟨r.1, hr⟩ : Fin (n' / 2)) = r := Fin.ext rfl
        let emb : Fin (n / 2) ↪ Fin (n' / 2) := ⟨Fin.castLE hle, Fin.castLE_injective hle⟩
        rw [← Finset.sum_subset (s₁ := Finset.univ.map emb) (Finset.subset_univ _), Finset.sum_map]
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hk : ((emb k : Fin (n' / 2)) : ℕ) < n / 2 := k.2
          rw [dite_eq_left hk]
          show W r (Fin.castLE hle k) * t ⟨k.1, hk⟩ c = W (Fin.castLE hle ⟨r.1, hr⟩) (Fin.castLE hle k) * t k c
          rw [hr']
        · intro k _ hk
          have : ¬ (k : ℕ) < n / 2 := fun e => hk (Finset.mem_map.2 ⟨⟨k.1, e⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          rw [dite_eq_right this, mul_zero]
      · refine Finset.sum_eq_zero fun k _ => ?_
        split_ifs with hk
        · rw [hWt (show k < r by rw [Fin.lt_def]; omega), zero_mul]
        · rw [mul_zero]
end
end

