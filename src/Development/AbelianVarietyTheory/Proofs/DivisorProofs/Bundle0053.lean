module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankISupEqOfISupIndep
section
namespace GlobalTheory

theorem iSupIndep_of_joint_eigen {E I : Type} [AddCommGroup E] [Module ℂ E]
    (h : I → Module.End ℂ E) (V : (I → ℂ) → Submodule ℂ E)
    (hV : ∀ x, ∀ v ∈ V x, ∀ i, h i v = x i • v) : iSupIndep V := by
  classical
  have stab : ∀ (s : Finset (I → ℂ)) (i : I), ∀ u ∈ ⨆ y ∈ s, V y, h i u ∈ ⨆ y ∈ s, V y := by
    intro s i
    have : (⨆ y ∈ s, V y) ≤ (⨆ y ∈ s, V y).comap (h i) := by
      refine iSup₂_le fun y hy v hv => ?_
      rw [Submodule.mem_comap, hV y v hv i]
      exact Submodule.smul_mem _ _ ((le_iSup₂_of_le (f := fun y (_ : y ∈ s) => V y) y hy le_rfl) hv)
    exact fun u hu => this hu
  have key : ∀ (x : I → ℂ) (s : Finset (I → ℂ)), x ∉ s → ∀ v ∈ V x, v ∈ (⨆ y ∈ s, V y) → v = 0 := by
    intro x s
    induction s using Finset.induction_on with
    | empty => intro _ v _ hv; simpa using hv
    | insert y s hy ih =>
      intro hx v hvx hv
      rw [Finset.mem_insert, not_or] at hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hv
      obtain ⟨w, hw, u, hu, hsum⟩ := hv
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx.1
      have e : (x i - y i) • v = h i u - y i • u := by
        rw [sub_smul, ← hV x v hvx i, ← hsum, map_add (f := _), hV y w hw i, smul_add]; abel
      have h0 := ih hx.2 ((x i - y i) • v) (Submodule.smul_mem _ _ hvx)
        (e ▸ Submodule.sub_mem _ (stab s i u hu) (Submodule.smul_mem _ _ hu))
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hi)
  intro x
  rw [Submodule.disjoint_def]
  intro v hvx hv
  replace hv : v ∈ ⨆ y : {y : I → ℂ // y ≠ x}, V y.1 := by rwa [iSup_subtype]
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv
  refine key x (s.image Subtype.val) ?_ v hvx ?_
  · intro hx
    obtain ⟨⟨y, hy⟩, -, e⟩ := Finset.mem_image.mp hx
    exact hy e
  · refine (iSup₂_le fun y hy => ?_ : (⨆ y ∈ s, V y.1) ≤ _) hs
    exact le_iSup₂_of_le (f := fun y (_ : y ∈ s.image Subtype.val) => V y) y.1
      (Finset.mem_image_of_mem _ hy) le_rfl

theorem finrank_iSup_eq_of_iSupIndep {E W X : Type} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (V : X → Submodule ℂ E) (V' : X → Submodule ℂ W) (hV : iSupIndep V) (hV' : iSupIndep V')
    (hd : ∀ x, Module.finrank ℂ (V x) = Module.finrank ℂ (V' x)) :
    Module.finrank ℂ (⨆ x, V x : Submodule ℂ E) = Module.finrank ℂ (⨆ x, V' x : Submodule ℂ W) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, Submodule.iSup_eq_range_dfinsupp_lsum]
  have e : ∀ x, V x ≃ₗ[ℂ] V' x := fun x => LinearEquiv.ofFinrankEq _ _ (hd x)
  exact (((LinearEquiv.ofInjective _ hV.dfinsupp_lsum_injective).symm.trans
    (DFinsupp.mapRange.linearEquiv e)).trans
      (LinearEquiv.ofInjective _ hV'.dfinsupp_lsum_injective)).finrank_eq

theorem finrank_iSup_joint_eigen_eq : ∀ {E W I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (h : I → Module.End ℂ E) (h' : I → Module.End ℂ W) (U : C → Submodule ℂ E) (U' : C → Submodule ℂ W) (lab : C → I → ℂ), (∀ c, ∀ x ∈ U c, ∀ i, h i x = lab c i • x) → (∀ c, ∀ x ∈ U' c, ∀ i, h' i x = lab c i • x) → (∀ c c', lab c = lab c' → U c = U c' ∧ U' c = U' c') → (∀ c, Module.finrank ℂ (U c) = Module.finrank ℂ (U' c)) → ∀ S : C → Prop, Module.finrank ℂ (⨆ (c : C) (_ : S c), U c : Submodule ℂ E) = Module.finrank ℂ (⨆ (c : C) (_ : S c), U' c : Submodule ℂ W) := by
  intro E W I C _ _ _ _ _ _ h h' U U' lab hU hU' hlab hd S
  have re : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F),
      (⨆ (c : C) (_ : S c), A c) = ⨆ (x : I → ℂ), ⨆ (c : C) (_ : S c ∧ lab c = x), A c := by
    intro F _ _ A
    apply le_antisymm
    · refine iSup₂_le fun c hc => le_iSup_of_le (lab c) ?_
      exact le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl
    · exact iSup_le fun x => iSup₂_le fun c hc =>
        le_iSup₂_of_le (f := fun c' (_ : S c') => A c') c hc.1 le_rfl
  have one : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F),
      (∀ c c', lab c = lab c' → A c = A c') → ∀ c, S c →
      (⨆ (c' : C) (_ : S c' ∧ lab c' = lab c), A c') = A c := by
    intro F _ _ A hA c hc
    apply le_antisymm
    · exact iSup₂_le fun c' hc' => (hA c' c hc'.2).le
    · exact le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl
  have none : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F) (x : I → ℂ),
      (¬ ∃ c, S c ∧ lab c = x) → (⨆ (c' : C) (_ : S c' ∧ lab c' = x), A c') = ⊥ := by
    intro F _ _ A x hx
    exact le_bot_iff.mp (iSup₂_le fun c hc => (hx ⟨c, hc⟩).elim)
  have ind : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (g : I → Module.End ℂ F)
      (A : C → Submodule ℂ F), (∀ c c', lab c = lab c' → A c = A c') →
      (∀ c, ∀ x ∈ A c, ∀ i, g i x = lab c i • x) →
      iSupIndep fun x : I → ℂ => ⨆ (c : C) (_ : S c ∧ lab c = x), A c := by
    intro F _ _ g A hA hg
    refine iSupIndep_of_joint_eigen g _ fun x v hv i => ?_
    by_cases hx : ∃ c, S c ∧ lab c = x
    · obtain ⟨c, hc, rfl⟩ := hx
      rw [one A hA c hc] at hv
      exact hg c v hv i
    · rw [none A x hx, Submodule.mem_bot] at hv
      simp [hv]
  rw [re U, re U']
  refine finrank_iSup_eq_of_iSupIndep _ _ (ind h U (fun c c' e => (hlab c c' e).1) hU)
    (ind h' U' (fun c c' e => (hlab c c' e).2) hU') fun x => ?_
  by_cases hx : ∃ c, S c ∧ lab c = x
  · obtain ⟨c, hc, rfl⟩ := hx
    rw [one U (fun c c' e => (hlab c c' e).1) c hc, one U' (fun c c' e => (hlab c c' e).2) c hc]
    exact hd c
  · rw [none U x hx, none U' x hx]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKaehlerEqOfUniversalTangent
section
open TrivSqZeroExt

namespace GlobalTheory

theorem finrank_kaehler_eq_of_universal_tangent :
    ∀ (R A k : Type) [CommRing R] [CommRing A] [Algebra R A] [Field k] (n d : ℕ)
    [Module.Free A (Ω[A⁄R])] [Module.Finite A (Ω[A⁄R])], Module.finrank A (Ω[A⁄R]) = n →
    ∀ (φ : A →+* k) (ψ : A →+* TrivSqZeroExt k (Fin d → k)),
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ →
    ψ.comp (algebraMap R A) = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (algebraMap R A)) →
    (∀ v : A →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
      v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) →
      ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ) → d = n := by
  intro R A k _ _ _ _ n d _ _ hn φ ψ hfst hR huniv
  classical
  haveI : Nontrivial A := φ.domain_nontrivial
  letI : Algebra A k := φ.toAlgebra
  letI : Algebra R k := (φ.comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A k := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hψf : ∀ a, (ψ a).fst = φ a := fun a => by
    simpa using RingHom.congr_fun hfst a
  have hψR : ∀ r, (ψ (algebraMap R A r)).snd = 0 := fun r => by
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hR r)
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using this
  have hsA : ∀ (a : A) (x : k), a • x = φ a * x := fun a x => rfl
  have hsR : ∀ (r : R) (x : k), r • x = φ (algebraMap R A r) * x := fun r x => rfl

  let E : Derivation R A (Fin d → k) := Derivation.mk'
    { toFun := fun a => (ψ a).snd
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        funext i
        simp [Algebra.smul_def, hψR, hψf, hsR, RingHom.algebraMap_toAlgebra] }
    (fun a b => by
      funext i
      simp [hψf, hsA, mul_comm])
  have hE : ∀ a, E a = (ψ a).snd := fun a => rfl
  let El : Ω[A⁄R] →ₗ[A] (Fin d → k) := E.liftKaehlerDifferential
  have hEl : ∀ a, El (KaehlerDifferential.D R A a) = (ψ a).snd := fun a => by
    simp [El, hE]
  let b : Module.Basis (Fin n) A (Ω[A⁄R]) := Module.finBasisOfFinrankEq A _ hn
  have hcA : ∀ (c : (Fin d → k) →ₗ[k] k) (a : A) (x : Fin d → k), c (a • x) = a • c x :=
    fun c a x => by
      have : a • x = φ a • x := rfl
      rw [this, c.map_smul]; rfl
  let cA : ((Fin d → k) →ₗ[k] k) → ((Fin d → k) →ₗ[A] k) := fun c =>
    { toFun := c, map_add' := c.map_add, map_smul' := hcA c }
  have hcA' : ∀ c x, cA c x = c x := fun _ _ => rfl
  have hc1 : ∀ c : (Fin d → k) →ₗ[k] k,
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp ((TrivSqZeroExt.map c).toRingHom.comp ψ) = φ :=
    fun c => by
      ext a
      simp [hψf]
  have hc2 : ∀ c : (Fin d → k) →ₗ[k] k,
      ((TrivSqZeroExt.map c).toRingHom.comp ψ).comp (algebraMap R A) =
        (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) := fun c => by
    ext r
    · simp [hψf, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [hψR, TrivSqZeroExt.algebraMap_eq_inl]
  let L : ((Fin d → k) →ₗ[k] k) →ₗ[k] (Fin n → k) :=
    LinearMap.pi (fun i => LinearMap.applyₗ (R := k) (El (b i)))
  have hL : ∀ c i, L c i = c (El (b i)) := fun _ _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : (cA c).comp El = 0 := b.ext fun i => by
      simpa [hL, hcA'] using congrFun hc i
    have h0' : ∀ a, c (ψ a).snd = 0 := fun a => by
      have := LinearMap.congr_fun h0 (KaehlerDifferential.D R A a)
      simpa [hEl, hcA'] using this
    have heq : (TrivSqZeroExt.map c).toRingHom.comp ψ = (TrivSqZeroExt.map 0).toRingHom.comp ψ := by
      ext a
      · simp
      · simp [h0']
    exact (huniv _ (hc1 c) (hc2 c)).unique rfl heq
  have hsurj : Function.Surjective L := by
    intro f
    let g : Ω[A⁄R] →ₗ[A] k := b.constr A f
    let Df : Derivation R A k := g.compDer (KaehlerDifferential.D R A)
    let v : A →+* DualNumber k :=
      { toFun := fun a => TrivSqZeroExt.inl (φ a) + TrivSqZeroExt.inr (Df a)
        map_one' := by ext <;> simp
        map_mul' := fun a a' => by ext <;> simp [hsA, mul_comm, add_comm]
        map_zero' := by ext <;> simp
        map_add' := fun a a' => by ext <;> simp [add_add_add_comm] }
    have hv1 : (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ := by
      ext a
      simp [v]
    have hv2 : v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) := by
      ext r
      · simp [v, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [v, TrivSqZeroExt.algebraMap_eq_inl]
    obtain ⟨c, hc, -⟩ := huniv v hv1 hv2
    have key : ∀ a, Df a = c (ψ a).snd := fun a => by
      have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hc a)
      simpa [v] using this
    have hg : (cA c).comp El = g := Derivation.liftKaehlerDifferential_unique _ _
      (Derivation.ext fun a => by simp [hEl, hcA', ← key, Df])
    refine ⟨c, funext fun i => ?_⟩
    rw [hL, ← hcA' c, ← LinearMap.comp_apply, hg]
    simp [g]
  have e := (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_linearMap, Module.finrank_fin_fun, Module.finrank_fin_fun, Module.finrank_self] at e
  simpa using e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
section
open Polynomial
namespace GlobalTheory

private lemma rank_submatrix_fromBlocks_one_zero_eq {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    (a b : ℕ) (e : m ≃ Fin a ⊕ Fin b) :
    ((Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 (0 : Matrix (Fin b) (Fin b) F)).submatrix
      e e).rank = a := by
  classical
  have hd : (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 (0 : Matrix (Fin b) (Fin b) F)) =
      Matrix.diagonal (Sum.elim (fun _ => (1 : F)) (fun _ => 0)) := by
    rw [← Matrix.fromBlocks_diagonal]
    simp
  rw [Matrix.rank_submatrix, hd, Matrix.rank_diagonal]
  simp [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]


open Matrix in
theorem eigDim_rank_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVd : IsUnit (V.map φ).det := by
    rw [show (V.map φ).det = φ V.det from (RingHom.map_det φ V).symm]
    exact ((Matrix.isUnit_iff_isUnit_det V).mp hV).map φ
  have hUd : IsUnit (U.map φ).det := by
    rw [show (U.map φ).det = φ U.det from (RingHom.map_det φ U).symm]
    exact ((Matrix.isUnit_iff_isUnit_det U).mp hU).map φ
  have h' : V.map φ * M.map φ * U.map φ =
      (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0
        (0 : Matrix (Fin (Fintype.card n - M.rank)) (Fin (Fintype.card n - M.rank)) L)).submatrix
          e e := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]
    simp [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  calc (M.map φ).rank = (V.map φ * M.map φ * U.map φ).rank := by
        rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUd,
          Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVd]
    _ = M.rank := by rw [h']; exact rank_submatrix_fromBlocks_one_zero_eq _ _ e

private lemma finrank_ker_toLin'_add_rank_eq_card {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n L) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' A)) + A.rank = Fintype.card n := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  rw [Matrix.toLin'_apply'] at h ⊢
  rw [Module.finrank_pi] at h
  unfold Matrix.rank
  omega

theorem eigDim_ker_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (M.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := finrank_ker_toLin'_add_rank_eq_card (M.map φ)
  have h2 := finrank_ker_toLin'_add_rank_eq_card M
  rw [eigDim_rank_map] at h1
  omega

theorem eigDim_aeval_toLin' {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    aeval (Matrix.toLin' M) f = Matrix.toLin' (aeval M f) :=
  Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] _) M f

theorem eigDim_aeval_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    (aeval M f).map φ = aeval (M.map φ) (f.map φ) := by
  have h : (φ.mapMatrix : Matrix n n K →+* Matrix n n L).comp (algebraMap K (Matrix n n K)) =
      (algebraMap L (Matrix n n L)).comp φ := by
    ext r i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  change φ.mapMatrix (Polynomial.eval₂ (algebraMap K (Matrix n n K)) M f) =
    Polynomial.eval₂ (algebraMap L (Matrix n n L)) (M.map φ) (f.map φ)
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, h]
  rfl

theorem eigDim_ker_aeval_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    Module.finrank L (LinearMap.ker (aeval (Matrix.toLin' (M.map φ)) (f.map φ))) =
      Module.finrank K (LinearMap.ker (aeval (Matrix.toLin' M) f)) := by
  rw [eigDim_aeval_toLin', eigDim_aeval_toLin', ← eigDim_aeval_map, eigDim_ker_map]

theorem eigDim_ker_mul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {p q : K[X]} (h : IsCoprime p q) :
    Module.finrank K (LinearMap.ker (aeval T (p * q))) =
      Module.finrank K (LinearMap.ker (aeval T p)) +
        Module.finrank K (LinearMap.ker (aeval T q)) := by
  rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime T h]
  have hd := Polynomial.disjoint_ker_aeval_of_isCoprime T h
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval T p))
    (LinearMap.ker (aeval T q))
  rw [hd.eq_bot] at hs
  simpa using hs

theorem eigDim_ker_prod {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (s : Finset K) :
    Module.finrank K (LinearMap.ker (aeval T (∏ z ∈ s, (X - C z)))) =
      ∑ z ∈ s, Module.finrank K (LinearMap.ker (aeval T (X - C z))) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, map_one, Module.End.one_eq_id, LinearMap.ker_id]
    simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, eigDim_ker_mul T, ih]
    refine IsCoprime.prod_right fun z hz => ?_
    refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ?_).isUnit
    rintro rfl
    exact ha hz

theorem finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace :
    ∀ (F : Type) [Field F] [Finite F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (f : F[X]) (y : AlgebraicClosure F), Irreducible f → aeval y f = 0 → Module.finrank F (LinearMap.ker (aeval (Matrix.toLin' M) f)) = f.natDegree * Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)))) y) := by
  intro F _ _ ι _ _ M f y hf hy
  classical
  rw [← eigDim_ker_aeval_map (algebraMap F (AlgebraicClosure F)) M f]
  set g := f.map (algebraMap F (AlgebraicClosure F)) with hg
  set T := Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F))) with hT
  have hsep : g.Separable := (PerfectField.separable_of_irreducible hf).map
  have hne : g ≠ 0 := Polynomial.map_ne_zero hf.ne_zero
  have hnd := Polynomial.nodup_roots hsep
  have hcard : Multiset.card g.roots = g.natDegree :=
    (IsAlgClosed.splits g).natDegree_eq_card_roots.symm
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hprod : (g.roots.map fun a => X - C a).prod = ∏ a ∈ g.roots.toFinset, (X - C a) := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have hker : aeval T g = g.leadingCoeff • aeval T (∏ a ∈ g.roots.toFinset, (X - C a)) := by
    conv_lhs => rw [← hfac, hprod]
    rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hterm : ∀ a ∈ g.roots.toFinset, Module.finrank (AlgebraicClosure F) (LinearMap.ker (aeval T (X - C a))) =
      Module.finrank (AlgebraicClosure F) (Module.End.eigenspace T y) := by
    intro a ha
    have haroot : aeval a f = 0 := by
      have h0 := Polynomial.IsRoot.eq_zero ((Polynomial.mem_roots hne).mp (Multiset.mem_toFinset.mp ha))
      rwa [hg, Polynomial.eval_map_algebraMap] at h0
    have hmin : minpoly F a = minpoly F y := by
      rw [← minpoly.eq_of_irreducible hf haroot, ← minpoly.eq_of_irreducible hf hy]
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp ((Normal.minpoly_eq_iff_mem_orbit (AlgebraicClosure F)).mp hmin)
    rw [AlgEquiv.smul_def] at hσ
    have hmat : (M.map (algebraMap F (AlgebraicClosure F)) - y • (1 : Matrix ι ι (AlgebraicClosure F))).map (σ : AlgebraicClosure F →+* AlgebraicClosure F) = M.map (algebraMap F (AlgebraicClosure F)) - a • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij, hσ]
    have e1 : aeval T (X - C a) = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - a • 1) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, hT,
        map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
    have e2 : T - y • 1 = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - y • 1) := by
      rw [hT, map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
    rw [Module.End.eigenspace_def, e1, e2, ← hmat, eigDim_ker_map]
  rw [hker, LinearMap.ker_smul _ _ hlc, eigDim_ker_prod, Finset.sum_congr rfl hterm,
    Finset.sum_const, smul_eq_mul, Multiset.toFinset_card_of_nodup hnd, hcard, hg,
    Polynomial.natDegree_map]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardValues
section
open Filter Topology

namespace GlobalTheory

theorem finrank_le_card_values : ∀ (C V Γ : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u = ν v → ∃ c : C, u - c • v = 0 ∨ ν u < ν (u - c • v)) → ∀ (F : Submodule C V) [Module.Finite C F], ∃ f : Fin (Module.finrank C F) → V, (∀ i, f i ∈ F ∧ f i ≠ 0) ∧ Function.Injective (fun i => ν (f i)) := by
  intro C V Γ _ _ _ _ ν _h1 _h2 h3 F _
  classical
  set S : Set Γ := ν '' {u | u ∈ F ∧ u ≠ 0} with hS
  have hg : ∀ s ∈ S, ∃ u, (u ∈ F ∧ u ≠ 0) ∧ ν u = s := fun s hs => hs
  choose! g hgF hgν using hg
  suffices hcard : ∃ e : Fin (Module.finrank C F) → Γ, Function.Injective e ∧ ∀ i, e i ∈ S by
    obtain ⟨e, he, heS⟩ := hcard
    refine ⟨fun i => g (e i), fun i => hgF _ (heS i), ?_⟩
    intro i j hij
    simp only at hij
    rw [hgν _ (heS i), hgν _ (heS j)] at hij
    exact he hij
  by_cases hfin : S.Finite
  · have key : ∀ n : ℕ, ∀ u, u ∈ F → u ≠ 0 →
        (hfin.toFinset.filter (fun s => ν u < s)).card = n →
        u ∈ Submodule.span C (g '' S) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro u huF hu0 hn
      have huS : ν u ∈ S := ⟨u, ⟨huF, hu0⟩, rfl⟩
      obtain ⟨hgF', hg0⟩ := hgF _ huS
      obtain ⟨c, hc⟩ := h3 u (g (ν u)) hu0 hg0 (hgν _ huS).symm
      have hgmem : g (ν u) ∈ Submodule.span C (g '' S) := Submodule.subset_span ⟨ν u, huS, rfl⟩
      have hdec : u = (u - c • g (ν u)) + c • g (ν u) := (sub_add_cancel _ _).symm
      rw [hdec]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hgmem)
      rcases hc with hc | hc
      · rw [hc]; exact Submodule.zero_mem _
      · by_cases hw0 : u - c • g (ν u) = 0
        · rw [hw0]; exact Submodule.zero_mem _
        · have hwF : u - c • g (ν u) ∈ F := F.sub_mem huF (F.smul_mem c hgF')
          refine ih _ ?_ _ hwF hw0 rfl
          rw [← hn]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨ν (u - c • g (ν u)), ?_, ?_⟩
            · rw [Finset.mem_filter, Set.Finite.mem_toFinset]
              exact ⟨⟨_, ⟨hwF, hw0⟩, rfl⟩, hc⟩
            · rw [Finset.mem_filter]
              exact fun h => lt_irrefl _ h.2
          · intro s hs
            rw [Finset.mem_filter] at hs ⊢
            exact ⟨hs.1, lt_trans hc hs.2⟩
    have hle : F ≤ Submodule.span C (g '' S) := by
      intro u huF
      by_cases hu0 : u = 0
      · rw [hu0]; exact Submodule.zero_mem _
      · exact key _ u huF hu0 rfl
    have himg : g '' S = ((hfin.toFinset.image g : Finset V) : Set V) := by
      ext x; simp
    have hdim : Module.finrank C F ≤ hfin.toFinset.card := by
      rw [himg] at hle
      calc Module.finrank C F ≤ Module.finrank C (Submodule.span C ((hfin.toFinset.image g : Finset V) : Set V)) :=
            Submodule.finrank_mono hle
        _ ≤ (hfin.toFinset.image g).card := finrank_span_finset_le_card _
        _ ≤ hfin.toFinset.card := Finset.card_image_le
    let emb : Fin (Module.finrank C F) ↪ hfin.toFinset :=
      (Fin.castLEEmb hdim).trans hfin.toFinset.equivFin.symm.toEmbedding
    refine ⟨fun i => (emb i : Γ), ?_, ?_⟩
    · intro i j hij
      exact emb.injective (Subtype.ext hij)
    · intro i
      exact (Set.Finite.mem_toFinset hfin).1 (emb i).2
  · let emb : ℕ ↪ S := Set.Infinite.natEmbedding S hfin
    refine ⟨fun i => (emb i : Γ), ?_, fun i => (emb i).2⟩
    intro i j hij
    exact Fin.ext (emb.injective (Subtype.ext hij))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfVolumeImageEqZero
section
open Set Filter Topology MeasureTheory

namespace GlobalTheory

theorem finrank_range_fderiv_lt_of_volume_image_eq_zero :
    ∀ (n : ℕ) (h : (Fin n → ℂ) → (Fin n → ℂ)) (W : Set (Fin n → ℂ)), IsOpen W → AnalyticOnNhd ℂ h W → volume (h '' W) = 0 → ∀ y ∈ W, Module.finrank ℂ (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) < n := by
  intro n h W hW ha h0 y hy
  by_contra hlt
  have hn : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  have hle := Submodule.finrank_le
    (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
  have htop : LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  have hs : HasStrictFDerivAt h (fderiv ℂ h y) y := (ha y hy).hasStrictFDerivAt
  have hmap := hs.map_nhds_eq_of_surj htop
  have hmem : h '' W ∈ 𝓝 (h y) := by
    rw [← hmap]
    exact image_mem_map (hW.mem_nhds hy)
  exact (Measure.measure_pos_of_mem_nhds volume hmem).ne' h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdZpowAdd
section
namespace GlobalTheory.ProductZpowAdd

theorem prod_zpow_add {F : Type} [inst : Field F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i : Fin (d + 1), x i ≠ 0) (m n : Fin (d + 1) → ℤ) :
    ∏ j : Fin (d + 1), x j ^ (m j + n j)
      = (∏ j : Fin (d + 1), x j ^ m j) * ∏ j : Fin (d + 1), x j ^ n j := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (hx j) _ _

end GlobalTheory.ProductZpowAdd
end

