module

public import Mathlib
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory

theorem exists_mem_proj_eq_on_finset {G ι : Type} [Group G] {Gv : ι → Type}
    [∀ v, Group (Gv v)] (π : ∀ v, G →* Gv v) (H : Subgroup G) (Kv : ∀ v, Subgroup (Gv v))
    (hH : ∀ v, ∀ h ∈ Kv v, ∃ g ∈ H, π v g = h ∧ ∀ w, w ≠ v → π w g = 1)
    (h : ∀ v, Gv v) (hh : ∀ v, h v ∈ Kv v) (T : Finset ι) :
    ∃ g ∈ H, (∀ v ∈ T, π v g = h v) ∧ ∀ v, v ∉ T → π v g = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, H.one_mem, by simp, by simp⟩
  | insert a T ha ih =>
    obtain ⟨g, hg, h1, h2⟩ := ih
    obtain ⟨g', hg', h3, h4⟩ := hH a (h a) (hh a)
    refine ⟨g' * g, H.mul_mem hg' hg, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [map_mul, h3, h2 _ ha, mul_one]
      · have hne : v ≠ a := fun e => ha (e ▸ hv)
        rw [map_mul, h4 v hne, h1 v hv, one_mul]
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, h4 v hv.1, h2 v hv.2, one_mul]

theorem index_pi_univ_dep {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod_local :
    ∀ (G ι : Type) [Group G] (Gv : ι → Type) [∀ v, Group (Gv v)] (π : ∀ v, G →* Gv v)
      (H K U : Subgroup G) (Kv Uv : ∀ v, Subgroup (Gv v)) (S : Finset ι),
      (∀ v, ∀ h ∈ Kv v, ∃ g ∈ H, π v g = h ∧ ∀ w, w ≠ v → π w g = 1) →
      (∀ g, g ∈ K ↔ g ∈ H ∧ ∀ v, π v g ∈ Kv v) →
      (∀ g, g ∈ U ↔ g ∈ H ∧ ∀ v, π v g ∈ Uv v) →
      (∀ v, v ∉ S → Kv v ≤ Uv v) →
      U.relIndex K = ∏ v ∈ S, (Uv v).relIndex (Kv v) := by
  intro G ι _ Gv _ π H K U Kv Uv S hH hK hU hS
  classical
  let f : K →* (∀ v : S, Kv v) :=
    { toFun := fun g v => ⟨π v g, ((hK g).1 g.2).2 v⟩
      map_one' := by
        funext v
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        funext v
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    intro x
    let h : ∀ v, Gv v := fun v => if hv : v ∈ S then (x ⟨v, hv⟩ : Gv v) else 1
    have hh : ∀ v, h v ∈ Kv v := by
      intro v
      by_cases hv : v ∈ S
      · simp only [h, dif_pos hv]; exact (x ⟨v, hv⟩).2
      · simp only [h, dif_neg hv]; exact (Kv v).one_mem
    obtain ⟨g, hg, h1, h2⟩ := exists_mem_proj_eq_on_finset π H Kv hH h hh S
    have hgK : g ∈ K := by
      refine (hK g).2 ⟨hg, fun v => ?_⟩
      by_cases hv : v ∈ S
      · rw [h1 v hv]; exact hh v
      · rw [h2 v hv]; exact (Kv v).one_mem
    refine ⟨⟨g, hgK⟩, ?_⟩
    funext v
    apply Subtype.ext
    change π v g = _
    rw [h1 v v.2]
    simp only [h, dif_pos v.2]
  have hc : U.subgroupOf K =
      (Subgroup.pi Set.univ fun v : S => (Uv v).subgroupOf (Kv v)).comap f := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hU]
    constructor
    · rintro ⟨-, h⟩ v -
      exact Subgroup.mem_subgroupOf.2 (h v)
    · intro h
      refine ⟨((hK g).1 g.2).1, fun v => ?_⟩
      by_cases hv : v ∈ S
      · exact Subgroup.mem_subgroupOf.1 (h ⟨v, hv⟩ (Set.mem_univ _))
      · exact hS v hv (((hK g).1 g.2).2 v)
  rw [Subgroup.relIndex, hc, Subgroup.index_comap_of_surjective _ hf, index_pi_univ_dep]
  exact Finset.prod_coe_sort S (fun v => (Uv v).relIndex (Kv v))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnitriGlEquiv
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.UniIndexPrime

theorem diag_mul {k : ℕ} {A : Type} [CommRing A] {x y : Matrix (Fin k) (Fin k) A}
    (hx : ∀ i j, j < i → x i j = 0) (hy : ∀ i j, j < i → y i j = 0) (i : Fin k) :
    (x * y) i i = x i i * y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hx i j h, zero_mul]
  · rw [hy j i h, mul_zero]

def uniSub (k : ℕ) (A : Type) [CommRing A] : Subgroup (GL (Fin k) A) where
  carrier := upperUni k A
  one_mem' := fun i j => ⟨fun h => by simp [Matrix.one_apply_ne h.ne'], by simp⟩
  mul_mem' := by
    intro x y hx hy i j
    have bx : BlockTriangular (x : Matrix (Fin k) (Fin k) A) id := fun a b h => (hx a b).1 h
    have by' : BlockTriangular (y : Matrix (Fin k) (Fin k) A) id := fun a b h => (hy a b).1 h
    refine ⟨fun h => (bx.mul by') h, ?_⟩
    rw [Units.val_mul, diag_mul (fun a b h => (hx a b).1 h) (fun a b h => (hy a b).1 h),
      (hx i i).2, (hy i i).2, one_mul]
  inv_mem' := by
    intro x hx i j
    have bx : BlockTriangular (x : Matrix (Fin k) (Fin k) A) id := fun a b h => (hx a b).1 h
    letI : Invertible (x : Matrix (Fin k) (Fin k) A) := x.invertible
    have bi : BlockTriangular ((x⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) id := by
      rw [Matrix.coe_units_inv]
      exact blockTriangular_inv_of_blockTriangular bx
    refine ⟨fun h => bi h, ?_⟩
    have h := diag_mul (fun a b h => (hx a b).1 h) (fun a b h => bi (show id b < id a from h)) i
    rw [Units.mul_inv, (hx i i).2, one_mul] at h
    simpa using h.symm

theorem closure_eq (k : ℕ) (A : Type) [CommRing A] :
    Subgroup.closure (upperUni k A) = uniSub k A := Subgroup.closure_eq (uniSub k A)

theorem mem_uniSub {k : ℕ} {A : Type} [CommRing A] (x : GL (Fin k) A) :
    x ∈ uniSub k A ↔ IsUnitri (x : Matrix (Fin k) (Fin k) A) :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩,
    fun h i j => ⟨h.1 i j, h.2 i⟩⟩

def glEquiv (k : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    GL (Fin k) A ≃* GL (Fin k) B :=
  Units.mapEquiv (e.mapMatrix (m := Fin k)).toMulEquiv

theorem glEquiv_apply (k : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (x : GL (Fin k) A) (i j : Fin k) :
    (glEquiv k e x : Matrix (Fin k) (Fin k) B) i j = e ((x : Matrix (Fin k) (Fin k) A) i j) := rfl

theorem isUnitri_glEquiv (k : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (x : GL (Fin k) A) :
    IsUnitri (x : Matrix (Fin k) (Fin k) A) ↔
      IsUnitri (glEquiv k e x : Matrix (Fin k) (Fin k) B) := by
  simp only [IsUnitri, glEquiv_apply, EmbeddingLike.map_eq_zero_iff, EmbeddingLike.map_eq_one_iff]

theorem index_upperUni : ∀ (κ : Type) [CommRing κ] (g k : ℕ), g.Prime → Nat.card κ = g →
    (((Subgroup.closure (upperUni k κ)).index : ℕ) : ℝ) = idxColLoc g k := by
  intro κ _ g k hg hc
  haveI : Finite κ := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
  letI : Fintype κ := Fintype.ofFinite κ
  have e : ZMod g ≃+* κ := ZMod.ringEquivOfPrime κ hg (by rw [← Nat.card_eq_fintype_card, hc])
  have h1 : Nat.card (GL (Fin k) (ZMod g)) = Nat.card (GL (Fin k) κ) :=
    Nat.card_congr (glEquiv k e).toEquiv
  have h2 : Nat.card {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      Nat.card (uniSub k κ) :=
    Nat.card_congr ((glEquiv k e).toEquiv.subtypeEquiv fun x =>
      (isUnitri_glEquiv k e x).trans (mem_uniSub _).symm)
  have h3 : (Nat.card (uniSub k κ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := uniSub k κ)).ne'
  rw [closure_eq, idxColLoc, idxLoc, h1, h2, eq_div_iff h3]
  exact_mod_cast (uniSub k κ).index_mul_card

end GlobalTheory.UniIndexPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.LatticeStabLocal

section Gen
variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type}
  {R : Type} [CommRing R] [Algebra F R] (T : Subring R) (N : Submodule (𝓞 E) (n → E))
  {k : ℕ} (s : Fin k → N)

def IsComb (u : n → E ⊗[F] R) : Prop :=
  ∃ a : Fin k → R, (∀ j, a j ∈ T) ∧ ∀ i, u i = ∑ j, (s j : n → E) i ⊗ₜ[F] a j

variable {T N s}

theorem isComb_zero : IsComb (F := F) T N s 0 :=
  ⟨0, fun _ => zero_mem _, fun i => by simp⟩

theorem IsComb.add {y z : n → E ⊗[F] R} (hy : IsComb T N s y) (hz : IsComb T N s z) :
    IsComb T N s (y + z) := by
  obtain ⟨a, ha, ea⟩ := hy
  obtain ⟨b, hb, eb⟩ := hz
  exact ⟨a + b, fun j => add_mem (ha j) (hb j), fun i => by
    simp only [Pi.add_apply, ea, eb, TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem IsComb.neg {y : n → E ⊗[F] R} (hy : IsComb T N s y) : IsComb T N s (-y) := by
  obtain ⟨a, ha, ea⟩ := hy
  exact ⟨-a, fun j => neg_mem (ha j), fun i => by
    simp only [Pi.neg_apply, ea, TensorProduct.tmul_neg, Finset.sum_neg_distrib]⟩

theorem isComb_tmul (hs : Submodule.span ℤ (Set.range s) = ⊤) {w : n → E} (hw : w ∈ N) {a : R}
    (ha : a ∈ T) : IsComb (F := F) T N s (fun i => w i ⊗ₜ[F] a) := by
  have : (⟨w, hw⟩ : N) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  have e : w = ∑ j, m j • (s j : n → E) := by simpa using (congrArg Subtype.val hm).symm
  refine ⟨fun j => m j • a, fun j => zsmul_mem ha _, fun i => ?_⟩
  rw [e]
  simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.sum_tmul]
  exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _

theorem IsComb.smul (hs : Submodule.span ℤ (Set.range s) = ⊤) {t : E ⊗[F] R}
    (ht : t ∈ tensInt (F := F) R (intOE E) T) :
    ∀ {y : n → E ⊗[F] R}, IsComb T N s y → IsComb T N s (t • y) := by
  refine Subring.closure_induction
    (p := fun t _ => ∀ {y : n → E ⊗[F] R}, IsComb T N s y → IsComb T N s (t • y))
    ?_ ?_ ?_ ?_ ?_ ?_ ht
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩) y ⟨a, ha, ea⟩
    · have : ((algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : R)) • y : n → E ⊗[F] R) =
          ∑ j, fun i => (e' • (s j : n → E)) i ⊗ₜ[F] a j := by
        funext i
        rw [Pi.smul_apply, ea, smul_eq_mul, Finset.mul_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
      change IsComb T N s ((algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : R)) • y)
      rw [this]
      exact Finset.sum_induction _ (IsComb T N s) (fun _ _ hx hy => hx.add hy) isComb_zero
        fun j _ => isComb_tmul hs (N.smul_mem e' (s j).2) (ha j)
    · refine ⟨fun j => b * a j, fun j => mul_mem hb (ha j), fun i => ?_⟩
      change ((1 : E) ⊗ₜ[F] b) * y i = _
      rw [ea, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · intro y _; rw [zero_smul]; exact isComb_zero
  · intro y hy; rwa [one_smul]
  · intro a b _ _ ha hb y hy; rw [add_smul]; exact (ha hy).add (hb hy)
  · intro a _ ha y hy; rw [neg_smul]; exact (ha hy).neg
  · intro a b _ _ ha hb y hy; rw [mul_smul]; exact ha (hb hy)

theorem mem_latS_iff_isComb (hs : Submodule.span ℤ (Set.range s) = ⊤) (u : n → E ⊗[F] R) :
    u ∈ latS R (tensInt (F := F) R (intOE E) T) N ↔ IsComb T N s u := by
  constructor
  · intro hu
    unfold latS at hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact isComb_tmul hs hw (one_mem T)
    | zero => exact isComb_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul t x _ hx => exact IsComb.smul hs t.2 hx
  · rintro ⟨a, ha, ea⟩
    have e : u = ∑ j, (⟨(1 : E) ⊗ₜ[F] a j, Subring.subset_closure (Or.inr ⟨⟨a j, ha j⟩, rfl⟩)⟩ :
        tensInt (F := F) R (intOE E) T) • fun i => inclE (F := F) R ((s j : n → E) i) := by
      funext i
      rw [ea, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      change _ = ((1 : E) ⊗ₜ[F] a j) * ((s j : n → E) i ⊗ₜ[F] (1 : R))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s j, (s j).2, rfl⟩)

end Gen

section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : Type}
  (N : Submodule (𝓞 E) (n → E))

theorem mem_latS_adele_iff [Module.Finite (𝓞 E) N] (u : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ latS (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) N ↔
      ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈
        latS (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E)
          (v.adicCompletionIntegers F).toSubring) N := by
  have : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := N)
  simp only [mem_latS_iff_isComb hs]
  constructor
  · rintro ⟨a, ha, ea⟩ v
    refine ⟨fun j => a j v, fun j => ha j v, fun i => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ea, map_sum]
    rfl
  · intro h
    choose a ha ea using h
    let A : Fin k → FiniteAdeleRing (𝓞 F) F :=
      fun j => ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    refine ⟨A, fun j v => ha v j, fun i => ?_⟩
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, map_sum]
    exact ea v i

theorem prV_mulVec [Fintype n] (v : HeightOneSpectrum (𝓞 F))
    (M : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (u : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (fun i => prV (E := E) v ((M *ᵥ u) i)) =
      M.map (prV (E := E) v) *ᵥ fun i => prV (E := E) v (u i) := by
  funext i
  exact RingHom.map_mulVec _ M u i

theorem mem_stabGL_adele_iff [Fintype n] [DecidableEq n] [Module.Finite (𝓞 E) N]
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    g ∈ stabGL (latS (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) N) ↔
      ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈
        stabGL (latS (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E)
          (v.adicCompletionIntegers F).toSubring) N) := by
  constructor
  · intro hg v x
    have key := hg fun i => Formalism.UG.P.afsplitIE v (x i)
    rw [mem_latS_adele_iff, mem_latS_adele_iff] at key
    simp only [prV_mulVec] at key
    have h0 : ∀ w, w ≠ v → (fun i => prV (E := E) w (Formalism.UG.P.afsplitIE v (x i))) = 0 :=
      fun w hw => funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v w hw _
    have h1 : (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE v (x i))) = x :=
      funext fun i => Formalism.UG.P.afsplit_prV_IE v _
    rw [Formalism.UG.P.afsplit_coe_bc_prV]
    constructor
    · intro hx
      have := key.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [h1]; exact hx
        · rw [h0 w hw]; exact zero_mem _) v
      rwa [h1] at this
    · intro hx
      have := key.2 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [h1]; exact hx
        · rw [h0 w hw, Matrix.mulVec_zero]; exact zero_mem _) v
      rwa [h1] at this
  · intro h u
    rw [mem_latS_adele_iff, mem_latS_adele_iff]
    refine forall_congr' fun v => ?_
    rw [prV_mulVec]
    exact h v _

end Adelic

theorem mem_levelAfL_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) N → ∀ g, g ∈ levelAfL σ J N ↔ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈ levelVL σ J v N := by
  intro F E _ _ _ _ _ σ n J N hN g
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
    exact ⟨h1, fun v => Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem σ J v g h1,
      (mem_stabGL_adele_iff N g).1 h2 v⟩⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_inf.2 ⟨h1, (mem_stabGL_adele_iff N g).2 fun v => (Subgroup.mem_inf.1 (h2 v)).2⟩

end GlobalTheory.LatticeStabLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitStabGLIffMemRange
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory

theorem stabGL_iff_conj_stdLat {A : Type} [CommRing A] (S : Subring A) {n : Type} [Fintype n]
    [DecidableEq n] (b : GL n A) (Λ : Submodule S (n → A))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) (g : GL n A) :
    g ∈ stabGL Λ ↔ b⁻¹ * g * b ∈ stabGL (stdLat (n := n) (A := A) S) := by
  have key : ∀ x : n → A, x ∈ Λ ↔ (b⁻¹).1 *ᵥ x ∈ stdLat (n := n) (A := A) S := fun x => by
    rw [hΛ, Formalism.UG.P.afsplit_mem_stdLat]
  constructor
  · intro hg y
    have h := hg (b.1 *ᵥ y)
    rw [key, key] at h
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.val_mul,
      Matrix.mul_assoc] using h
  · intro hg x
    have h := hg ((b⁻¹).1 *ᵥ x)
    rw [key, key]
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.mul_one, Units.val_mul,
      Matrix.mul_assoc] using h

theorem conj_mem_UJ_one {A : Type} [CommRing A] (τ : A →+* A) {n : Type} [Fintype n]
    [DecidableEq n] (J : Matrix n n A) (b : GL n A) (hb : cT τ b.1 * J * b.1 = 1)
    (g : GL n A) (hg : g ∈ UJ τ J) : b⁻¹ * g * b ∈ UJ τ (1 : Matrix n n A) := by
  have hg' : cT τ g.1 * J * g.1 = J := hg
  have cm : ∀ M N : Matrix n n A, cT τ (M * N) = cT τ N * cT τ M := fun M N => by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  have c1 : cT τ (1 : Matrix n n A) = 1 := by
    simp only [cT, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]
  have hJ : cT τ (b⁻¹).1 * (b⁻¹).1 = J := by
    calc cT τ (b⁻¹).1 * (b⁻¹).1 = cT τ (b⁻¹).1 * (cT τ b.1 * J * b.1) * (b⁻¹).1 := by
          rw [hb, Matrix.mul_one]
      _ = cT τ (b.1 * (b⁻¹).1) * J * (b.1 * (b⁻¹).1) := by
          rw [cm]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, c1, Matrix.one_mul, Matrix.mul_one]
  change cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1 = 1
  calc cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1
      = cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
        simp only [Units.val_mul, cm, Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [hJ, hg', hb]

theorem split_stabGL_iff_mem_range :
    ∀ (A K : Type) [CommRing A] [Field K] (O : ValuationSubring K) (S : Subring A) (τ : A →+* A) (φ : A ≃+* K × K), (∀ x, φ (τ x) = swapR K (φ x)) → (∀ x, x ∈ S ↔ (φ x).1 ∈ O ∧ (φ x).2 ∈ O) → ∀ (n : Type) [Fintype n] [DecidableEq n] (J : Matrix n n A) (b : GL n A) (Λ : Submodule S (n → A)), cT τ b.1 * J * b.1 = 1 → (∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) → ∀ g ∈ UJ τ J, g ∈ stabGL Λ ↔ (bc ((RingHom.fst K K).comp φ.toRingHom) b)⁻¹ * bc ((RingHom.fst K K).comp φ.toRingHom) g * bc ((RingHom.fst K K).comp φ.toRingHom) b ∈ (bc (n := n) (algebraMap O K)).range := by
  intro A K _ _ O S τ φ hτ hS n _ _ J b Λ hb hΛ g hg
  have hU := conj_mem_UJ_one τ J b hb g hg
  rw [stabGL_iff_conj_stdLat S b Λ hΛ g, ← map_inv, ← map_mul, ← map_mul]
  generalize b⁻¹ * g * b = h at hU
  have hinj : Function.Injective (algebraMap O K) := Subtype.val_injective
  have hOr : ∀ x : K, x ∈ Set.range (algebraMap O K) ↔ x ∈ O :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rw [Formalism.UG.P.afsplit_stab_iff, Formalism.UG.P.levelvsplit_mem_range_iff _ hinj, ← map_inv,
    Formalism.UG.P.levelvsplit_coe_bc, Formalism.UG.P.levelvsplit_coe_bc]
  simp only [hOr, hS]
  have main : ∀ k : GL n A, k ∈ UJ τ (1 : Matrix n n A) → ∀ i j,
      (φ (k.1 i j)).2 = (φ ((k⁻¹).1 j i)).1 := by
    intro k hk i j
    have rel := Formalism.UG.P.levelvsplit_unitary τ φ hτ _ k hk
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at rel
    have hk1 : k.1.map ((RingHom.fst K K).comp φ.toRingHom) *
        (k⁻¹).1.map ((RingHom.fst K K).comp φ.toRingHom) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have s := Formalism.UG.P.levelvsplit_solve 1 1 _ _ _ (Matrix.mul_one _) hk1 rel
    rw [Matrix.one_mul, Matrix.mul_one] at s
    exact congrFun (congrFun s i) j
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (h1 i j).1, fun i j => (h2 i j).1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ⟨h1 i j, ?_⟩, fun i j => ⟨h2 i j, ?_⟩⟩
    · rw [main h hU]; exact h2 j i
    · rw [main h⁻¹ (inv_mem hU), inv_inv]; exact h1 j i

end GlobalTheory
end

