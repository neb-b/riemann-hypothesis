module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0007
public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.SumPlSingle

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.CMAdele
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_re (hF : IsTotallyReal F) (s : InfinitePlace F → ℝ) : ∃ a : AF F, (∀ u : AF F, evI F u = 0 → u * a = 0) ∧
    ∀ w, InfinitePlace.Completion.extensionEmbedding w (a.1 w) = s w := by
  refine ⟨((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (s w)), 0),
    fun u hu => ?_, fun w => ?_⟩
  · have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  · rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
    congr 1
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (s w)

theorem exists_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) :
    ∃ a : AE F E, At (evI F) a ∧ ∀ w, piInf (τ w) a = c w := by
  obtain ⟨β, hβ⟩ := exists_moved h
  obtain ⟨t, ht, ht'⟩ := exists_re h.1 fun w => (c w).im / ((τ w).1 β).im
  obtain ⟨s, hs, hs'⟩ := exists_re h.1 fun w => (c w).re - (c w).im / ((τ w).1 β).im * ((τ w).1 β).re
  refine ⟨s ⊗ₜ[F] 1 + t ⊗ₜ[F] β, fun u hu => ?_, fun w => ?_⟩
  · rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hs u hu, ht u hu,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · have := im_ne_zero h hβ (τ w).1
    rw [map_add (f := _), piInf_tmul, piInf_tmul, hs', ht', map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; field_simp; ring

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul', show star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) = _ from
      Complex.conj_eq_iff_im.2 (im_extension h.1 w _)]

def atI (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : Ideal (AE F E) where
  carrier := {a | At (evI F) a}
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => smul_zero u
  smul_mem' := fun c a ha u hu => by rw [smul_eq_mul, ← mul_smul_comm, ha u hu, mul_zero]

theorem mem_atI {a : AE F E} : a ∈ atI F E ↔ At (evI F) a := Iff.rfl

theorem at_entry {m n : Type} {M : Matrix m n (AE F E)} (h : At (evI F) M) (i j) : M i j ∈ atI F E :=
  fun u hu => congrFun (congrFun (h u hu) i) j

theorem at_cA {a : AE F E} (h : a ∈ atI F E) : cA σ a ∈ atI F E := fun u hu => by rw [← map_smul, h u hu, map_zero]

theorem eq_of_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {a b : AE F E} (hab : a - b ∈ atI F E)
    (e : ∀ w, piInf (τ w) a = piInf (τ w) b) : a = b :=
  sub_eq_zero.1 (eq_zero_of_piInf σ h τ _ hab fun w => by rw [map_sub, e, sub_self])

theorem exists_unit (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) (hc : ∀ w, c w ≠ 0) :
    ∃ t : (AE F E)ˣ, (t : AE F E) - 1 ∈ atI F E ∧ ∀ w, piInf (τ w) t = c w := by
  obtain ⟨a, ha, ha'⟩ := exists_inf h τ fun w => c w - 1
  obtain ⟨b, hb, hb'⟩ := exists_inf h τ fun w => (c w)⁻¹ - 1
  refine ⟨Units.mkOfMulEqOne (1 + a) (1 + b) (eq_of_inf h τ ?_ fun w => ?_), by simpa [mem_atI] using ha, fun w => by simp [ha']⟩
  · rw [show (1 + a) * (1 + b) - 1 = a * (1 + b) + b by ring]
    exact add_mem (Ideal.mul_mem_right _ _ ha) hb
  · simp [ha', hb', hc w]

theorem inv_at {t : (AE F E)ˣ} (h : (t : AE F E) - 1 ∈ atI F E) : ((t⁻¹ : (AE F E)ˣ) : AE F E) - 1 ∈ atI F E := by
  have := neg_mem (Ideal.mul_mem_left _ ((t⁻¹ : (AE F E)ˣ) : AE F E) h)
  rwa [mul_sub, Units.inv_mul, mul_one, neg_sub] at this

theorem absE_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {t : (AE F E)ˣ} (ht : (t : AE F E) - 1 ∈ atI F E) :
    (absE F E t : ℝ) = ∏ w, ‖piInf (τ w) t‖ ^ 2 := by
  have e : ∀ v, GlobalTheory.Doubling.unitFin F E v t = 1 := fun v => by
    obtain ⟨u, hu, hu'⟩ : ∃ u : AF F, evI F u = 0 ∧ evFin F v u = 1 :=
      ⟨(0, 1), map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), map_one (evalV F v)⟩
    have h0 : algebraMap (AF F) (AE F E) u * ((t : AE F E) - 1) = 0 := (Algebra.smul_def _ _).symm.trans (ht u hu)
    have h1 := congrArg (compFin F E v) h0
    have h2 : compFin F E v (algebraMap (AF F) (AE F E) u) = 1 := by
      change evFin F v u ⊗ₜ[F] (1 : E) = 1
      rw [hu']; rfl
    rw [map_mul, map_zero, h2, one_mul, map_sub, map_one, sub_eq_zero] at h1
    exact Units.ext h1
  rw [GlobalTheory.Doubling.absE_apply]
  simp only [e, map_one, finprod_one, mul_one, GlobalTheory.Doubling.absEw_eq_sq h (τ _)]
  push_cast
  rfl

theorem exists_torus (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (l : InfinitePlace F → ℂ) (χ : Chr F E)
    {m : InfinitePlace F → ℤ} (hχ : HasExp τ χ m) (r : ℝ) :
    ∃ (t : ℝ → (AE F E)ˣ) (c : ℂ), (∀ s, (t s : AE F E) - 1 ∈ atI F E ∧ ∀ w, piInf (τ w) (t s) = Complex.exp (s * l w)) ∧
      HasDerivAt (fun s => (χ (t s) : ℂ) * (((absE F E (t s) : ℝ) ^ r : ℝ) : ℂ)) c 0 := by
  choose t ht ht' using fun s : ℝ => exists_unit h τ (fun w => Complex.exp (s * l w)) fun w => Complex.exp_ne_zero _
  have e : (fun s => (χ (t s) : ℂ) * (((absE F E (t s) : ℝ) ^ r : ℝ) : ℂ)) =
      fun s : ℝ => Complex.exp (s * ∑ w, ((l w - (l w).re) * m w + 2 * (l w).re * r)) := by
    funext s
    rw [hχ _ (ht s), absE_inf h τ (ht s), Finset.mul_sum, Complex.exp_sum,
      ← Real.finsetProd_rpow _ _ fun _ _ => by positivity, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ht', Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_mul, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_sub,
      ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    simp only [Complex.re_ofReal_mul]
    push_cast; ring
  exact ⟨t, _, fun s => ⟨ht s, ht' s⟩, e ▸ ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const _).cexp⟩

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

-- bundled from Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ParZero
section
noncomputable section

open FockH1Action PositivityTheory.KReal

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {R S R₁ S₁ : ℕ}

structure Emb (R S R₁ S₁ : ℕ) where
  e : Ix R₁ S₁ → Ix R S
  i : Fin R
  j : Fin S
  ε : ℝ
  ε_ne : ε ≠ 0
  inj : Function.Injective e
  cover : ∀ a, a = .inl i ∨ a = .inr j ∨ ∃ b, e b = a
  ne_i : ∀ b, e b ≠ .inl i
  ne_j : ∀ b, e b ≠ .inr j
  sb : ∀ a b, sameBlock (e a) (e b) ↔ sameBlock a b
  pos : ∀ a b, posC a b → posC (e a) (e b)
  ext : ∀ a b, (a = .inl i ∨ a = .inr j) → sameBlock a (e b) → (0 < ε → posC a (e b)) ∧ (ε < 0 → posC (e b) a)


open Classical in
def Emb.h (m : Emb R S R₁ S₁) (a : Ix R S) : ℝ := if a = .inl m.i ∨ a = .inr m.j then m.ε else 0

theorem Emb.h_e (m : Emb R S R₁ S₁) (b) : m.h (m.e b) = 0 := if_neg (not_or.2 ⟨m.ne_i b, m.ne_j b⟩)

theorem Emb.h_s (m : Emb R S R₁ S₁) {a} (h : a = .inl m.i ∨ a = .inr m.j) : m.h a = m.ε := if_pos h

theorem Emb.cases (m : Emb R S R₁ S₁) (a : Ix R S) : (a = .inl m.i ∨ a = .inr m.j) ∨ ∃ b, m.e b = a := or_assoc.2 (m.cover a)

theorem Emb.eq_of (m : Emb R S R₁ S₁) {a b : Ix R S} (ha : a = .inl m.i ∨ a = .inr m.j) (hb : b = .inl m.i ∨ b = .inr m.j)
    (h : sameBlock a b) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | exact h.elim

theorem Emb.sum (m : Emb R S R₁ S₁) {N : Type} [AddCommMonoid N] (g : Ix R S → N) :
    ∑ a, g a = g (.inl m.i) + g (.inr m.j) + ∑ b, g (m.e b) := by
  classical
  have : (Finset.univ : Finset (Ix R S)) = insert (.inl m.i) (insert (.inr m.j) (Finset.univ.image m.e)) := by
    ext a; simpa using m.cover a
  rw [this, Finset.sum_insert, Finset.sum_insert, Finset.sum_image fun a _ b _ h => m.inj h, add_assoc]
  · simpa using m.ne_j
  · simpa using m.ne_i

variable {ι M M₁ : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] [AddCommGroup M₁] [Module ℂ M₁]

structure IsPar (m : Emb R S R₁ S₁) (act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M) (act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁)
    (c c' : ι → ℂ) (D : M →ₗ[ℂ] M₁) : Prop where
  levi : ∀ w a b x, D (act (un w (m.e a) (m.e b)) x) = act₁ (un w a b) (D x)
  cpt : ∀ w x, D (act (un w (.inl m.i) (.inl m.i) + un w (.inr m.j) (.inr m.j)) x) = c w • D x
  hyp : ∀ w x, D (act (un w (.inl m.i) (.inr m.j) + un w (.inr m.j) (.inl m.i)) x) = c' w • D x
  cen : ∀ w x, D (act (un w (.inl m.i) (.inl m.i) - un w (.inl m.i) (.inr m.j) + un w (.inr m.j) (.inl m.i) -
    un w (.inr m.j) (.inr m.j)) x) = 0
  n₁ : ∀ w b x, D (act (un w (m.e b) (.inl m.i) - un w (m.e b) (.inr m.j)) x) = 0
  n₂ : ∀ w b x, D (act (un w (.inl m.i) (m.e b) + un w (.inr m.j) (m.e b)) x) = 0

theorem IsPar.sub {m : Emb R S R₁ S₁} {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M}
    {act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁} {c c' : ι → ℂ} {D D' : M →ₗ[ℂ] M₁} (h : IsPar m act act₁ c c' D)
    (h' : IsPar m act act₁ c c' D') (t : ℂ) : IsPar m act act₁ c c' (D' - t • D) := by
  refine ⟨fun w a b x => ?_, fun w x => ?_, fun w x => ?_, fun w x => ?_, fun w b x => ?_, fun w b x => ?_⟩ <;>
    rw [LinearMap.sub_apply, LinearMap.smul_apply]
  · rw [h.levi, h'.levi, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul]
  · rw [h.cpt, h'.cpt, LinearMap.sub_apply, LinearMap.smul_apply, smul_sub, smul_comm t]
  · rw [h.hyp, h'.hyp, LinearMap.sub_apply, LinearMap.smul_apply, smul_sub, smul_comm t]
  · rw [h.cen, h'.cen, smul_zero, sub_zero]
  · rw [h.n₁, h'.n₁, smul_zero, sub_zero]
  · rw [h.n₂, h'.n₂, smul_zero, sub_zero]

theorem HWMod.centre {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M} {Λ : ι → Ix R S → ℂ} {f : M} (h : HWMod act Λ f) (w : ι) (x : M) :
    ∑ a, act (un w a a) x = (∑ a, Λ w a) • x := by
  have e : ∑ a, un w a a = (Pi.single w 1 : ι → Mat R S) := by
    funext i
    by_cases h : i = w
    · subst h
      simp only [un, Finset.sum_apply, Pi.single_eq_same]
      ext a b
      simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
      split_ifs with e
      · subst e; simp
      · exact Finset.sum_eq_zero fun c _ => if_neg fun h => e (h.1.symm.trans h.2)
    · simp [un, Pi.single_eq_of_ne h]
  have : (act (Pi.single w 1)).eigenspace (∑ a, Λ w a) = ⊤ := by
    refine h.gen _ ?_ fun Z _ y hy => ?_
    · rw [Module.End.mem_eigenspace_iff, ← e]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply, h.wt, Finset.sum_smul]
    · have := shift_eig h.lie (H := Pi.single w 1) (Z := Z) (k := 0) (by
        funext i
        by_cases h : i = w
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]) hy
      rwa [add_zero] at this
  have hx : x ∈ (act (Pi.single w 1)).eigenspace (∑ a, Λ w a) := this ▸ Submodule.mem_top
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Module.End.mem_eigenspace_iff, ← e, map_sum, LinearMap.sum_apply] at hx
  exact hx

theorem par_zero {m : Emb R S R₁ S₁} {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M}
    {act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁} {Λ : ι → Ix R S → ℂ} {f : M} (hM : HWMod act Λ f) {c c' : ι → ℂ}
    {D : M →ₗ[ℂ] M₁} (hD : IsPar m act act₁ c c' D) (hc : ∀ w, c w = Λ w (.inl m.i) + Λ w (.inr m.j)) (h0 : D f = 0) :
    D = 0 := by
  have hs : ∀ (g : Ix R S → ℂ), ∑ a, (m.h a : ℂ) * g a = m.ε * (g (.inl m.i) + g (.inr m.j)) := fun g => by
    rw [m.sum, m.h_s (.inl rfl), m.h_s (.inr rfl)]; simp [m.h_e, mul_add]
  have hlow : low (act (dg ι m.h)) (∑ w, ∑ a, m.h a * Λ w a) ≤ LinearMap.ker D := by
    refine low_ker D fun x => ?_
    rw [dg_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, Finset.sum_smul, hs]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← hc, mul_smul, ← hD.cpt, m.sum, m.h_s (.inl rfl), m.h_s (.inr rfl)]
    simp [m.h_e]
  obtain ⟨V, hV1, hV2, hV3⟩ := cyc_le hM.lie (sb := sameBlock) (pos := posC)
    (z := fun a b => sameBlock a b ∧ ∃ a' b', m.e a' = a ∧ m.e b' = b) (fun _ _ _ => sb_trans) sb_refl (fun _ _ => sb_of_pos) m.h
    (fun a b e => by
      rcases m.cases a with ha | ⟨a, rfl⟩ <;> rcases m.cases b with hb | ⟨b, rfl⟩
      · rw [m.h_s ha, m.h_s hb]
      · rw [m.h_s ha, m.h_e]
        exact not_lt.1 fun h => pos_asymm e ((m.ext a b ha (sb_of_pos e)).2 h)
      · rw [m.h_s hb, m.h_e]
        exact not_lt.1 fun h => pos_asymm e ((m.ext b a hb (sb_symm (sb_of_pos e))).1 h)
      · rw [m.h_e, m.h_e])
    (by rintro _ _ ⟨e, a, b, rfl, rfl⟩; exact ⟨e, by rw [m.h_e, m.h_e]⟩)
    (fun a b e e' => by
      rcases m.cases a with ha | ⟨a, rfl⟩ <;> rcases m.cases b with hb | ⟨b, rfl⟩
      · exact .inl (.inl (m.eq_of ha hb e))
      · rw [m.h_s ha, m.h_e] at e'
        exact .inl (.inr ((m.ext a b ha e).1 (e'.lt_of_ne m.ε_ne.symm)))
      · rw [m.h_s hb, m.h_e] at e'
        exact .inl (.inr ((m.ext b a hb (sb_symm e)).2 (e'.lt_of_ne m.ε_ne)))
      · exact .inr ⟨e, a, b, rfl, rfl⟩)
    hM.wt hM.pos (N := LinearMap.ker D) h0
    (by
      rintro w _ _ ⟨-, a, b, rfl, rfl⟩ x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hD.levi, hx, map_zero])
  have hVk : V ≤ LinearMap.ker D := hV2.trans (sup_le le_rfl hlow)
  set K := alg ι (sameBlock (p := R) (q := S))
  set P := stab act (LinearMap.ker D)
  have mP : ∀ Z (t : ℂ), (∀ x, D (act Z x) = t • D x) → Z ∈ K ⊔ P := fun Z t h => Submodule.mem_sup_right fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [h, hx, smul_zero]
  have mK : ∀ w {a b : Ix R S}, sameBlock a b → un w a b ∈ K ⊔ P := fun w _ _ e => Submodule.mem_sup_left (un_mem w e)
  have hij : ∀ w, un w (.inl m.i) (.inr m.j) ∈ K ⊔ P ∧ un w (.inr m.j) (.inl m.i) ∈ K ⊔ P := fun w => by
    have a1 := mP _ _ (hD.hyp w)
    have a2 := mP _ 0 fun x => (hD.cen w x).trans (zero_smul _ _).symm
    have a3 := mK w (sb_refl (.inl m.i : Ix R S))
    have a4 := mK w (sb_refl (.inr m.j : Ix R S))
    constructor
    · convert Submodule.smul_mem _ (1 / 2 : ℂ) (sub_mem (add_mem (sub_mem a1 a2) a3) a4) using 1
      module
    · convert Submodule.smul_mem _ (1 / 2 : ℂ) (add_mem (sub_mem (add_mem a1 a2) a3) a4) using 1
      module
  have tri : ∀ b : Ix R S, sameBlock b (.inl m.i) ∨ sameBlock b (.inr m.j) := fun b => by cases b <;> simp [sameBlock]
  have hb : ∀ w b, (un w (m.e b) (.inl m.i) ∈ K ⊔ P ∧ un w (m.e b) (.inr m.j) ∈ K ⊔ P) ∧
      un w (.inl m.i) (m.e b) ∈ K ⊔ P ∧ un w (.inr m.j) (m.e b) ∈ K ⊔ P := fun w b => by
    have a1 := mP _ 0 fun x => (hD.n₁ w b x).trans (zero_smul _ _).symm
    have a2 := mP _ 0 fun x => (hD.n₂ w b x).trans (zero_smul _ _).symm
    rcases tri (m.e b) with e | e
    · have a3 := mK w e
      have a4 := mK w (sb_symm e)
      exact ⟨⟨a3, by simpa using sub_mem a3 a1⟩, a4, by simpa using sub_mem a2 a4⟩
    · have a3 := mK w e
      have a4 := mK w (sb_symm e)
      exact ⟨⟨by simpa using add_mem a1 a3, a3⟩, by simpa using sub_mem a2 a4, a4⟩
  have top : (⊤ : Submodule ℂ (ι → Mat R S)) ≤ K ⊔ P := by
    refine le_trans (fun Z _ => ?_ : _ ≤ alg ι fun _ _ => True) (alg_le fun w a b _ => ?_)
    · exact fun _ _ _ h => (h trivial).elim
    · rcases m.cover a with rfl | rfl | ⟨a, rfl⟩ <;> rcases m.cover b with rfl | rfl | ⟨b, rfl⟩
      exacts [mK w (sb_refl _), (hij w).1, (hb w b).2.1, (hij w).2, mK w (sb_refl _), (hb w b).2.2, (hb w a).1.1, (hb w a).1.2,
        Submodule.mem_sup_right fun x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hD.levi, hx, map_zero]]
  obtain ⟨W, hW1, hW2, hW3⟩ := gen_le hM.lie (g := ⊤) (q := K) (l := P) (fun _ _ _ _ => trivial) le_top le_top top hV3 hVk
    fun Z hZ => hZ
  rw [hM.gen W (hW1 hV1) hW3] at hW2
  exact LinearMap.ker_eq_top.1 (top_le_iff.1 hW2)

theorem par_line {m : Emb R S R₁ S₁} {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M}
    {act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁} {Λ : ι → Ix R S → ℂ} {Λ₁ : ι → Ix R₁ S₁ → ℂ} {f : M} {f₁ : M₁}
    (hM : HWMod act Λ f) (hM₁ : HWMod act₁ Λ₁ f₁) (hΛ : ∀ w b, Λ w (m.e b) = Λ₁ w b) {c c' : ι → ℂ}
    {D D' : M →ₗ[ℂ] M₁} (hD : IsPar m act act₁ c c' D) (hD' : IsPar m act act₁ c c' D') (h0 : D ≠ 0) :
    ∃ t : ℂ, D' = t • D := by
  obtain ⟨x, hx⟩ : ∃ x, D x ≠ 0 := by
    by_contra h
    exact h0 (LinearMap.ext fun x => not_not.1 fun e => h ⟨x, e⟩)
  have hc : ∀ w, c w = Λ w (.inl m.i) + Λ w (.inr m.j) := fun w => by
    have e := congrArg D (hM.centre w x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [m.sum, m.sum, map_add (f := _), ← LinearMap.add_apply, ← map_add act, hD.cpt, map_sum, map_smul] at e
    simp only [hD.levi, hM₁.centre, hΛ] at e
    rw [← add_smul] at e
    exact add_right_cancel (smul_left_injective ℂ hx e)
  have val : ∀ {E : M →ₗ[ℂ] M₁}, IsPar m act act₁ c c' E → ∃ t : ℂ, E f = t • f₁ := fun {E} hE =>
    hM₁.one _ (fun w a => by rw [← hE.levi, hM.wt, map_smul, hΛ]) fun w a b e => by
      rw [← hE.levi, hM.pos w _ _ (m.pos a b e), map_zero]
  obtain ⟨t, ht⟩ := val hD
  obtain ⟨t', ht'⟩ := val hD'
  have t0 : t ≠ 0 := fun e => h0 (par_zero hM hD hc (by rw [ht, e, zero_smul]))
  refine ⟨t' / t, sub_eq_zero.1 (par_zero hM (hD.sub hD' _) hc ?_)⟩
  rw [LinearMap.sub_apply, LinearMap.smul_apply, ht, ht', smul_smul, div_mul_cancel₀ _ t0, sub_self]

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

