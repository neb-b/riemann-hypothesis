module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTrace
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckDecOfTrace

universe u

variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}

def homSub (hc : IsLinCat N Hom) (a b : O) : Submodule ℂ (N a →ₗ[ℂ] N b) where
  carrier := {f | Hom a b f}
  add_mem' := fun {f g} hf hg => hc.add a b f g hf hg
  zero_mem' := hc.zero a b
  smul_mem' := fun c f hf => hc.smul a b c f hf

def post (hc : IsLinCat N Hom) (a : O) {b c : O} (f : N b →ₗ[ℂ] N c) (hf : Hom b c f) :
    homSub hc a b →ₗ[ℂ] homSub hc a c where
  toFun w := ⟨f ∘ₗ w.1, hc.comp _ _ _ _ _ w.2 hf⟩
  map_add' v w := Subtype.ext (by simp [LinearMap.comp_add])
  map_smul' c w := Subtype.ext (by simp [LinearMap.comp_smul])

theorem exists_iso_of_eq (hc : IsLinCat N Hom) {a b : O} (h : a = b) :
    ∃ (θ : N a →ₗ[ℂ] N b) (θ' : N b →ₗ[ℂ] N a), Hom a b θ ∧ Hom b a θ' ∧ θ ∘ₗ θ' = LinearMap.id ∧
      θ' ∘ₗ θ = LinearMap.id := by
  subst h
  exact ⟨LinearMap.id, LinearMap.id, hc.id a, hc.id a, rfl, rfl⟩

theorem exists_basis (hc : IsLinCat N Hom) {P : Type} [DecidableEq P] {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr) (ν : P) :
    ∃ b : Module.Basis {k // par k = ν} ℂ (homSub hc (T ν) X),
      ∀ k, ∃ θ : N (T ν) →ₗ[ℂ] N (T (par k.1)), (b k).1 = io k.1 ∘ₗ θ := by
  classical
  have hex := fun k : {k // par k = ν} => exists_iso_of_eq hc (congrArg T k.2.symm)
  choose θ θ' hθ hθ' h1 h2 using hex
  let v : {k // par k = ν} → homSub hc (T ν) X := fun k =>
    ⟨io k.1 ∘ₗ θ k, hc.comp _ _ _ _ _ (hθ k) (hd.io_hom k.1)⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := hT.1 ν
    obtain ⟨x, hx⟩ := exists_ne (0 : N (T ν))
    have h3 := congrArg (fun w : homSub hc (T ν) X => θ' i (pr i.1 (w.1 x))) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [v, Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, Submodule.coe_zero, LinearMap.zero_apply, map_zero, LinearMap.comp_apply] at h3
    rw [Finset.sum_eq_single i] at h3
    · have e1 : pr i.1 (io i.1 (θ i x)) = θ i x := LinearMap.congr_fun (hd.pr_io i.1) _
      have e2 : θ' i (θ i x) = x := LinearMap.congr_fun (h2 i) _
      rw [e1, e2] at h3
      exact (smul_eq_zero.1 h3).resolve_right hx
    · intro k _ hk
      have e1 : pr i.1 (io k.1 (θ k x)) = 0 :=
        LinearMap.congr_fun (hd.pr_io_ne i.1 k.1 fun h => hk (Subtype.ext h.symm)) _
      rw [e1]; simp
    · simp
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro w _
    have hw : w = ∑ k, (⟨io k ∘ₗ (pr k ∘ₗ w.1), hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
        (hd.io_hom k)⟩ : homSub hc (T ν) X) := by
      apply Subtype.ext
      ext x
      have := LinearMap.congr_fun hd.sum (w.1 x)
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at this
      simp only [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.comp_apply, this]
    rw [hw]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : par k = ν
    · obtain ⟨c, hc'⟩ := hT.2.1 ν (θ' ⟨k, hk⟩ ∘ₗ (pr k ∘ₗ w.1))
        (hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k)) (hθ' ⟨k, hk⟩))
      have : (⟨io k ∘ₗ (pr k ∘ₗ w.1), hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
        (hd.io_hom k)⟩ : homSub hc (T ν) X) = c • v ⟨k, hk⟩ := by
        apply Subtype.ext
        ext x
        have e1 : θ' ⟨k, hk⟩ (pr k (w.1 x)) = c • x := LinearMap.congr_fun hc' x
        have e2 : θ ⟨k, hk⟩ (θ' ⟨k, hk⟩ (pr k (w.1 x))) = pr k (w.1 x) := LinearMap.congr_fun (h1 _) _
        rw [e1] at e2
        show io k (pr k (w.1 x)) = c • io k (θ ⟨k, hk⟩ x)
        rw [← e2, map_smul, map_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have h0 := hT.2.2 ν (par k) (Ne.symm hk) (pr k ∘ₗ w.1) (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
      have : (⟨io k ∘ₗ (pr k ∘ₗ w.1), hc.comp _ _ _ _ _ (hc.comp _ _ _ _ _ w.2 (hd.pr_hom k))
        (hd.io_hom k)⟩ : homSub hc (T ν) X) = 0 := by
        apply Subtype.ext
        simp [h0]
      rw [this]
      exact Submodule.zero_mem _
  exact ⟨Module.Basis.mk hli hsp, fun k => ⟨θ k, by rw [Module.Basis.mk_apply]⟩⟩

theorem exists_trace (hc : IsLinCat N Hom) {P : Type} [DecidableEq P] {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr) (ν : P)
    (Φ : Module.End ℂ (N X)) (a : κ → ℂ) (h : ∀ k, Φ ∘ₗ io k = a k • io k) :
    ∃ F : Module.End ℂ (homSub hc (T ν) X), (∀ w, (F w).1 = Φ ∘ₗ w.1) ∧
      LinearMap.trace ℂ _ F = ∑ k ∈ univ.filter (fun k => par k = ν), a k := by
  classical
  obtain ⟨b, hb⟩ := exists_basis hc hT hd ν
  refine ⟨b.constr ℂ fun k => a k.1 • b k, ?_, ?_⟩
  · have : (homSub hc (T ν) X).subtype ∘ₗ (b.constr ℂ fun k => a k.1 • b k) =
        (LinearMap.llcomp ℂ _ _ _ Φ) ∘ₗ (homSub hc (T ν) X).subtype := by
      refine b.ext fun k => ?_
      obtain ⟨θ, hθ⟩ := hb k
      simp only [LinearMap.comp_apply, Module.Basis.constr_basis, Submodule.subtype_apply,
        Submodule.coe_smul, LinearMap.llcomp_apply', hθ]
      rw [← LinearMap.comp_assoc, h, LinearMap.smul_comp]
    intro w
    exact LinearMap.congr_fun this w
  · rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace,
      Finset.sum_subtype (univ.filter fun k => par k = ν) (p := fun k => par k = ν) (by simp)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [LinearMap.toMatrix_apply]

theorem dec_of_gen (hc : IsLinCat N Hom) {P : Type} {T : P → O} (hT : IsSimpleFam Hom T)
    {κ : Type} [Fintype κ] {par : κ → P} {X Z : O} {io : ∀ k, N (T (par k)) →ₗ[ℂ] N X}
    {pr : ∀ k, N X →ₗ[ℂ] N (T (par k))} (hd : IsDec Hom X (fun k => T (par k)) io pr)
    {j : N Z →ₗ[ℂ] N X} {q : N X →ₗ[ℂ] N Z} (hj : Hom Z X j) (hq : Hom X Z q) (hqj : q ∘ₗ j = LinearMap.id)
    {I : Type} [Fintype I] {e : I → P} (he : Function.Injective e)
    (g : ∀ i, homSub hc (T (e i)) Z) (hg0 : ∀ i, g i ≠ 0) (hg : ∀ i w, ∃ c : ℂ, c • g i = w)
    (h0 : ∀ ν, (∀ i, e i ≠ ν) → ∀ w : homSub hc (T ν) Z, w = 0) :
    ∃ io pr, IsDec Hom Z (fun i => T (e i)) io pr := by
  classical
  let S : (N Z →ₗ[ℂ] N Z) → Prop := fun f =>
    ∃ r : ∀ i, homSub hc Z (T (e i)), ∑ i, (g i).1 ∘ₗ (r i).1 = f
  have S0 : S 0 := ⟨0, by simp⟩
  have Sadd : ∀ f f', S f → S f' → S (f + f') := by
    rintro _ _ ⟨r, rfl⟩ ⟨r', rfl⟩
    exact ⟨r + r', by simp [LinearMap.comp_add, Finset.sum_add_distrib]⟩
  have Sterm : ∀ ν (f : N (T ν) →ₗ[ℂ] N Z) (h : N Z →ₗ[ℂ] N (T ν)), Hom _ _ f → Hom _ _ h → S (f ∘ₗ h) := by
    intro ν f h hf hh
    by_cases hν : ∃ i, e i = ν
    · obtain ⟨i, rfl⟩ := hν
      obtain ⟨c, hc'⟩ := hg i ⟨f, hf⟩
      have hc'' : c • (g i).1 = f := congrArg Subtype.val hc'
      refine ⟨Pi.single i (c • ⟨h, hh⟩), ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [← hc'', LinearMap.comp_smul, LinearMap.smul_comp]
      · intro i' _ hi'
        simp [Pi.single_eq_of_ne hi']
      · simp
    · push Not at hν
      have : f = 0 := congrArg Subtype.val (h0 ν hν ⟨f, hf⟩)
      rw [this, LinearMap.zero_comp]
      exact S0
  have Sid : S LinearMap.id := by
    have : (LinearMap.id : N Z →ₗ[ℂ] N Z) = ∑ k, (q ∘ₗ io k) ∘ₗ (pr k ∘ₗ j) := by
      ext x
      have e1 := LinearMap.congr_fun hd.sum (j x)
      have e2 : q (j x) = x := LinearMap.congr_fun hqj x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at e1 ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, e1, e2]
    rw [this]
    exact Finset.sum_induction _ S Sadd S0 fun k _ =>
      Sterm _ _ _ (hc.comp _ _ _ _ _ (hd.io_hom k) hq) (hc.comp _ _ _ _ _ hj (hd.pr_hom k))
  obtain ⟨r, hr⟩ := Sid
  have hne : ∀ i i', i ≠ i' → (r i).1 ∘ₗ (g i').1 = 0 := fun i i' h =>
    hT.2.2 (e i') (e i) (fun h' => h (he h').symm) _ (hc.comp _ _ _ _ _ (g i').2 (r i).2)
  refine ⟨fun i => (g i).1, fun i => (r i).1, fun i => (g i).2, fun i => (r i).2, hr, fun i => ?_, hne⟩
  obtain ⟨c, hc'⟩ := hT.2.1 (e i) _ (hc.comp _ _ _ _ _ (g i).2 (r i).2)
  have h1 : (∑ i', (g i').1 ∘ₗ (r i').1) ∘ₗ (g i).1 = (g i).1 := by rw [hr, LinearMap.id_comp]
  have h2 : (∑ i', (g i').1 ∘ₗ (r i').1) ∘ₗ (g i).1 = c • (g i).1 := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    rw [Finset.sum_eq_single i]
    · have : (r i).1 ((g i).1 x) = c • x := LinearMap.congr_fun hc' x
      rw [this, map_smul]; rfl
    · intro i' _ hi'
      have : (r i').1 ((g i).1 x) = 0 := LinearMap.congr_fun (hne i' i hi') x
      rw [this, map_zero]
    · simp
  have h3 : (c - 1) • (g i).1 = 0 := by rw [sub_smul, one_smul, ← h2, h1, sub_self]
  have h4 : (g i).1 ≠ 0 := fun h => hg0 i (Subtype.ext h)
  have h5 : c = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right h4)
  rw [hc', h5, one_smul]

theorem decOfTrace : DecOfTrace := by
  intro O N _ _ Hom hc P _ T hT κ _ par X Z io₁ io₂ pr₁ pr₂ hd₁ hd₂ Φ Φ₁ Φ₂ a b cs α β h₁ h₂ hΦ j q hj hq
    hqj hβ hrel I _ e he hone hzero
  have key : ∀ ν, Module.Finite ℂ (homSub hc (T ν) Z) ∧
      β * (Module.finrank ℂ (homSub hc (T ν) Z) : ℂ) =
        ∑ k ∈ univ.filter (fun k => par k = ν), (a k + b k + α - cs ν) := by
    intro ν
    obtain ⟨bs, -⟩ := exists_basis hc hT hd₁ ν
    haveI : Module.Finite ℂ (homSub hc (T ν) X) := Module.Finite.of_basis bs
    have hid : post hc (T ν) q hq ∘ₗ post hc (T ν) j hj = LinearMap.id := by
      ext w x
      exact LinearMap.congr_fun hqj (w.1 x)
    haveI hfin : Module.Finite ℂ (homSub hc (T ν) Z) :=
      Module.Finite.of_surjective (post hc (T ν) q hq) fun w =>
        ⟨post hc (T ν) j hj w, LinearMap.congr_fun hid w⟩
    refine ⟨hfin, ?_⟩
    obtain ⟨F₁, hF₁, t₁⟩ := exists_trace hc hT hd₁ ν Φ₁ a h₁
    obtain ⟨F₂, hF₂, t₂⟩ := exists_trace hc hT hd₂ ν Φ₂ b h₂
    obtain ⟨F₃, hF₃, t₃⟩ := exists_trace hc hT hd₁ ν ((α - cs ν) • LinearMap.id) (fun _ => α - cs ν)
      (fun k => by ext x; simp)
    have hA : β • (post hc (T ν) j hj ∘ₗ post hc (T ν) q hq) = F₁ + F₂ + F₃ := by
      ext w x
      have e1 : Φ (w.1 x) = cs ν • w.1 x := LinearMap.congr_fun (hΦ ν w.1 w.2) x
      rw [hrel] at e1
      simp only [LinearMap.add_apply, Submodule.coe_add, hF₁, hF₂, hF₃, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearMap.id_apply, LinearMap.sub_apply] at e1 ⊢
      show β • j (q (w.1 x)) = _
      rw [sub_smul, ← e1]
      abel
    have ht := congrArg (LinearMap.trace ℂ _) hA
    rw [map_smul, LinearMap.trace_comp_comm', hid, LinearMap.trace_id, map_add (f := _), map_add (f := _), t₁, t₂, t₃,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, smul_eq_mul] at ht
    rw [ht]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hgen : ∀ i, ∃ g : homSub hc (T (e i)) Z, g ≠ 0 ∧ ∀ w, ∃ c : ℂ, c • g = w := by
    intro i
    have h := (key (e i)).2
    rw [hone i] at h
    have h' : (Module.finrank ℂ (homSub hc (T (e i)) Z) : ℂ) = 1 :=
      mul_left_cancel₀ hβ (by rw [h, mul_one])
    exact finrank_eq_one_iff'.1 (by exact_mod_cast h')
  choose g hg0 hg using hgen
  refine dec_of_gen hc hT hd₁ hj hq hqj he g hg0 hg fun ν hν w => ?_
  obtain ⟨hfin, h⟩ := key ν
  rw [hzero ν hν] at h
  have h' : Module.finrank ℂ (homSub hc (T ν) Z) = 0 := by
    exact_mod_cast (mul_eq_zero.1 h).resolve_left hβ
  exact finrank_zero_iff_forall_zero.1 h' w

end GlobalTheory.CompanionTheory.ZuckDecOfTrace
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesAdjoint
section
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu

namespace GlobalTheory.CompanionTheory.BmuDsAd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem ex_mul_eq {y : Mat n} (hy : IsUnit y) (X : Mat n) (t : ℝ) :
    ex X t * y = y * ex (y⁻¹ * X * y) t := by
  have hd : IsUnit y.det := (Matrix.isUnit_iff_isUnit_det y).1 hy
  have h1 : (t : ℂ) • (y⁻¹ * X * y) = y⁻¹ * ((t : ℂ) • X) * y := by
    simp [Matrix.mul_smul, Matrix.smul_mul]
  unfold ex
  rw [h1, Matrix.exp_conj' _ _ hy, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.one_mul]

theorem lie_conj {Hm y X : Mat n} (hy : IsUnit y) (hyH : yᴴ * Hm * y = Hm) (hX : Lie Hm X) :
    Lie Hm (y⁻¹ * X * y) := by
  have hd : IsUnit y.det := (Matrix.isUnit_iff_isUnit_det y).1 hy
  have h1 : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : Hm * y⁻¹ = yᴴ * Hm := by
    calc Hm * y⁻¹ = yᴴ * Hm * y * y⁻¹ := by rw [hyH]
      _ = yᴴ * Hm := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h3 : y⁻¹ᴴ * Hm = Hm * y := by
    calc y⁻¹ᴴ * Hm = y⁻¹ᴴ * (yᴴ * Hm * y) := by rw [hyH]
      _ = (y * y⁻¹)ᴴ * (Hm * y) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hm * y := by rw [h1]; simp
  unfold Lie at hX ⊢
  calc (y⁻¹ * X * y)ᴴ * Hm + Hm * (y⁻¹ * X * y)
      = yᴴ * Xᴴ * (y⁻¹ᴴ * Hm) + (Hm * y⁻¹) * X * y := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = yᴴ * (Xᴴ * Hm + Hm * X) * y := by
        rw [h2, h3]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX]; simp

theorem dsAd : DsAd := by
  intro n Hm H _ _ _ σ hσ y hy W hW
  have hyu : IsUnit y := by
    have hyH : yᴴ * Hm * y = Hm := hy
    have h1 : (Hm * yᴴ * Hm) * y = 1 := by
      rw [Matrix.mul_assoc Hm, Matrix.mul_assoc Hm, hyH, hσ.sq]
    exact (Matrix.isUnit_iff_isUnit_det y).2 (Matrix.isUnit_det_of_left_inverse h1)
  have hyH : yᴴ * Hm * y = Hm := hy
  have hL : ∀ W, LieWd Hm W → LieWd Hm (W.map fun X => y⁻¹ * X * y) := by
    intro W hW Z hZ
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hZ
    exact lie_conj hyu hyH (hW X hX)
  refine ⟨hL W hW, fun u hu => ?_⟩
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : LieWd Hm W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hX : Lie Hm X := hW X List.mem_cons_self
    have hX' : ∀ t, ex (y⁻¹ * X * y) t ∈ UH Hm := fun t => ex_mem_of_lie (lie_conj hyu hyH hX) t
    have hs : IsSm (UH Hm) σ (dsW σ (W.map fun X => y⁻¹ * X * y) u) :=
      hu.dsW hσ.rep fun Z hZ t => ex_mem_of_lie (hL W hW' Z hZ) t
    rw [List.map_cons, dsW_cons, dsW_cons, ih hW',
      apply_ds hσ.rep hX' hy (hs.differentiableAt hσ.rep hX')]
    unfold ds
    congr 1
    ext t
    rw [← hσ.rep.apply_mul (ex_mem_of_lie hX t) hy, ex_mul_eq hyu]

end GlobalTheory.CompanionTheory.BmuDsAd
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsFactor
section
open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuFactor

theorem exists_factor {S E V : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (J : S →ₗ[ℂ] E) (B : S →ₗ[ℂ] V) (C : ℝ)
    (hb : ∀ v, ‖B v‖ ≤ C * ‖J v‖) : ∃ T : E →L[ℂ] V, ∀ v, B v = T (J v) := by
  have hker : LinearMap.ker J ≤ LinearMap.ker B := fun v hv => by
    have := hb v
    rw [LinearMap.mem_ker.1 hv, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let g : LinearMap.range J →ₗ[ℂ] V := ((LinearMap.ker J).liftQ B hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hg : ∀ v : S, g ⟨J v, LinearMap.mem_range_self J v⟩ = B v := fun v => by
    show (LinearMap.ker J).liftQ B hker (J.quotKerEquivRange.symm ⟨J v, _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]; rfl
  have hgb : ∀ y : LinearMap.range J, ‖g y‖ ≤ C * ‖y‖ := by
    rintro ⟨_, v, rfl⟩
    exact (congrArg norm (hg v)).le.trans (hb v)
  obtain ⟨T, hT⟩ := ContinuousLinearMap.exist_extension_of_finiteDimensional_range (g.mkContinuous _ hgb)
  refine ⟨T, fun v => ?_⟩
  have := congrArg (fun f => f ⟨J v, LinearMap.mem_range_self J _⟩) hT
  exact (hg v).symm.trans this

theorem factor : Factor := by
  intro n Hm H _ _ _ σ hσ V _ _ _ B hB
  obtain ⟨C, Ws, hW, hC⟩ := hB.bd
  have h := hσ.rep
  have hI : ∀ i : Fin Ws.length, LieWd Hm (Ws.get i) := fun i => hW _ (List.get_mem Ws i)
  have hL : ∀ i : Fin Ws.length, LieW (UH Hm) (Ws.get i) := fun i X hX t => ex_mem_of_lie (hI i X hX) t
  let S : Submodule ℂ H :=
    { carrier := {v | IsSm (UH Hm) σ v}
      add_mem' := fun ha hb => IsSm.add ha hb
      zero_mem' := IsSm.zero
      smul_mem' := fun c _ ha => IsSm.smul ha c }
  let J : S →ₗ[ℂ] (Fin Ws.length → H) :=
    { toFun := fun v i => dsW σ (Ws.get i) v
      map_add' := fun a b => funext fun i => dsW_add h a.2 b.2 (hL i)
      map_smul' := fun c a => funext fun i => dsW_smul h a.2 c (hL i) }
  let B' : S →ₗ[ℂ] V :=
    { toFun := fun v => B v
      map_add' := fun a b => hB.add _ a.2 _ b.2
      map_smul' := fun c a => hB.smul c _ a.2 }
  have hb : ∀ v : S, ‖B' v‖ ≤ (|C| * Ws.length) * ‖J v‖ := fun v => by
    have h1 : (Ws.map fun w => ‖dsW σ w (v : H)‖).sum ≤ Ws.length * ‖J v‖ := by
      have := List.sum_le_card_nsmul (Ws.map fun w => ‖dsW σ w (v : H)‖) ‖J v‖ (by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.get_of_mem hw
        exact norm_le_pi_norm (J v) i)
      rwa [List.length_map, nsmul_eq_mul] at this
    have h0 : 0 ≤ (Ws.map fun w => ‖dsW σ w (v : H)‖).sum :=
      List.sum_nonneg fun x hx => by obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    calc ‖B' v‖ ≤ C * _ := hC _ v.2
      _ ≤ |C| * (Ws.length * ‖J v‖) := mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)
      _ = _ := by ring
  obtain ⟨T, hT⟩ := exists_factor J B' _ hb
  refine ⟨Ws.length, Ws.get, fun i => T.comp (ContinuousLinearMap.single ℂ (fun _ => H) i), hI, fun v hv => ?_⟩
  have h2 : B v = T (J ⟨v, hv⟩) := hT ⟨v, hv⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, ← Finset.univ_sum_single (J ⟨v, hv⟩), map_sum]
  rfl

end GlobalTheory.CompanionTheory.BmuFactor

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadratic
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.WedgeSplitCasimir

theorem jW_mul_transpose (n m : ℕ) (J J' : Sub n m) (s s' : Fin n) :
    (jW n m * (jW n m)ᵀ) (J, s) (J', s') =
      if s ∉ J.1 ∧ s' ∉ J'.1 ∧ insert s J.1 = insert s' J'.1 then
        (-1) ^ (J.1.filter fun a => a < s).card * (-1) ^ (J'.1.filter fun a => a < s').card else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, jW]
  by_cases hs : s ∈ J.1
  · simp [hs]
  · have hc : (insert s J.1).card = m + 1 := by rw [Finset.card_insert_of_notMem hs, J.2]
    rw [Finset.sum_eq_single (⟨insert s J.1, hc⟩ : Sub n (m + 1))]
    · by_cases h : s' ∉ J'.1 ∧ insert s J.1 = insert s' J'.1
      · rw [if_pos ⟨hs, rfl⟩, if_pos h, if_pos ⟨hs, h⟩]
      · rw [if_neg h, mul_zero, if_neg (fun h' => h h'.2)]
    · intro I _ hI
      rw [if_neg, zero_mul]
      rintro ⟨_, h⟩
      exact hI (Subtype.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem anticomm {n : ℕ} (J J' : Finset (Fin n)) (s s' : Fin n) :
    (if s ∈ J' ∧ s' ∉ J'.erase s ∧ J = insert s' (J'.erase s) then
        (-1 : ℂ) ^ ((J'.erase s).filter fun c => c < s').card * (-1) ^ ((J'.erase s).filter fun c => c < s).card
      else 0) =
    (if J = J' ∧ s = s' then 1 else 0) -
      if s ∉ J ∧ s' ∉ J' ∧ insert s J = insert s' J' then
        (-1) ^ (J.filter fun a => a < s).card * (-1) ^ (J'.filter fun a => a < s').card else 0 := by
  have sq : ∀ a : ℕ, (-1 : ℂ) ^ a * (-1) ^ a = 1 := fun a => by
    rw [← mul_pow]; simp
  by_cases hss : s = s'
  · subst hss
    by_cases hs : s ∈ J'
    · rw [Finset.insert_erase hs, sq]
      simp [hs]
    · by_cases hJ : J = J'
      · subst hJ
        simp [hs, sq]
      · rw [if_neg (fun h => hs h.1), if_neg (fun h => hJ h.1), if_neg, sub_zero]
        rintro ⟨h1, h2, h3⟩
        apply hJ
        rw [← Finset.erase_insert h1, h3, Finset.erase_insert h2]
  · rw [if_neg (fun h : J = J' ∧ s = s' => hss h.2), zero_sub]
    by_cases h : s ∈ J' ∧ s' ∉ J'.erase s ∧ J = insert s' (J'.erase s)
    · rw [if_pos h]
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨K, hK, rfl⟩ : ∃ K : Finset (Fin n), s ∉ K ∧ J' = insert s K :=
        ⟨J'.erase s, Finset.notMem_erase _ _, (Finset.insert_erase h1).symm⟩
      rw [Finset.erase_insert hK] at h2 h3 ⊢
      subst h3
      rw [if_pos ⟨by simp [hss, hK], by simp [Ne.symm hss, h2], Finset.insert_comm _ _ _⟩]
      rw [Finset.filter_insert, Finset.filter_insert]
      rcases lt_or_gt_of_ne hss with hlt | hlt
      · rw [if_neg (not_lt.2 hlt.le), if_pos hlt,
          Finset.card_insert_of_notMem (fun h => hK (Finset.mem_filter.1 h).1)]
        ring
      · rw [if_pos hlt, if_neg (not_lt.2 hlt.le),
          Finset.card_insert_of_notMem (fun h => h2 (Finset.mem_filter.1 h).1)]
        ring
    · rw [if_neg h, if_neg, neg_zero]
      rintro ⟨h1, h2, h3⟩
      apply h
      have hs : s ∈ J' := by
        have : s ∈ insert s' J' := h3 ▸ Finset.mem_insert_self s J
        exact (Finset.mem_insert.1 this).resolve_left hss
      refine ⟨hs, fun h => h2 (Finset.mem_of_mem_erase h), ?_⟩
      rw [← Finset.erase_insert h1, h3, Finset.erase_insert_of_ne (Ne.symm hss)]

theorem wedgeQ : StdD → (∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0) → WedgeQ := by
  intro hS hW k r m
  ext ⟨J, s⟩ ⟨J', s'⟩
  have h1 : qMat (wedge k r m) (vr k r false) (J, s) (J', s') =
      (wedge k r m).dC (Matrix.single s' s 1) J J' := by
    simp only [qMat, Matrix.sum_apply, Matrix.kroneckerMap_apply, (hS k r _).1]
    rw [Finset.sum_eq_single s', Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [ha]
    · simp
  rw [h1, hW, Matrix.sub_apply, jW_mul_transpose, anticomm, Matrix.one_apply]
  congr 1
  simp only [Prod.mk.injEq, Subtype.ext_iff]

end GlobalTheory.CompanionTheory.WedgeSplitCasimir
end

