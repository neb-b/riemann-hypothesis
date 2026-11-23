module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CloseVectorNeZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSup
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SupModel

variable {k G : Type} [Field k] [Group G]

theorem isHom_comp {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) :=
  fun s x => by simp only [LinearMap.comp_apply]; rw [hf, hg]

theorem isHom_add {A B : Ob k G} {f g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    (hf : IsHom A B f) (hg : IsHom A B g) : IsHom A B (f + g) :=
  fun s x => by simp only [LinearMap.add_apply, map_add (f := _)]; rw [hf, hg]

theorem exists_sum (A B : Ob k G) : ∃ (C : Ob k G) (i : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), IsHom A C i ∧ IsHom B C j ∧ Function.Bijective (i.coprod j) := by
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.prod B.ρ)
  refine ⟨C, e.toLinearMap ∘ₗ LinearMap.inl k _ _, e.toLinearMap ∘ₗ LinearMap.inr k _ _, ?_, ?_, ?_⟩
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]; congr 1; simp [Representation.prod]
  · have : (e.toLinearMap ∘ₗ LinearMap.inl k _ _).coprod (e.toLinearMap ∘ₗ LinearMap.inr k _ _)
        = e.toLinearMap := by
      rw [← LinearMap.comp_coprod, LinearMap.coprod_inl_inr, LinearMap.comp_id]
    rw [this]; exact e.bijective

theorem exists_proj {A B C : Ob k G} {i : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    {j : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hi : IsHom A C i) (hj : IsHom B C j)
    (hb : Function.Bijective (i.coprod j)) :
    ∃ (π : (Fin C.m → k) →ₗ[k] (Fin A.m → k)) (π' : (Fin C.m → k) →ₗ[k] (Fin B.m → k)),
      IsHom C A π ∧ IsHom C B π' ∧ (∀ x, π (i x) = x) ∧ (∀ x, π (j x) = 0) ∧ (∀ x, π' (i x) = 0) ∧
      (∀ x, π' (j x) = x) ∧ ∀ x, i (π x) + j (π' x) = x := by
  let e := LinearEquiv.ofBijective _ hb
  have h1 : ∀ x y, e.symm (i x + j y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; simp [e]
  have h2 : ∀ x, i (e.symm x).1 + j (e.symm x).2 = x := fun x => by
    exact e.apply_symm_apply x
  have h3 : ∀ g x, e.symm (C.ρ g x) = (A.ρ g (e.symm x).1, B.ρ g (e.symm x).2) := fun g x => by
    rw [← h1, hi, hj, ← map_add (f := _), h2]
  refine ⟨LinearMap.fst k _ _ ∘ₗ e.symm.toLinearMap, LinearMap.snd k _ _ ∘ₗ e.symm.toLinearMap,
    fun g x => ?_, fun g x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => h2 x⟩
  · simp [h3]
  · simp [h3]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]
  · have := h1 x 0; simp at this; simp [this]
  · have := h1 0 x; simp at this; simp [this]

variable {l n : ℕ} {R : RingPG k l}

theorem map_comp_apply (F : DFun R n G) {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} {h : (Fin A.m → k) →ₗ[k] (Fin C.m → k)}
    (hA : F.Obj A) (hB : F.Obj B) (hC : F.Obj C) (hf : IsHom A B f) (hg : IsHom B C g)
    (hh : ∀ x, g (f x) = h x) (i : ZMod n) (x : Vc k A.m) :
    F.map B C g i (F.map A B f i x) = F.map A C h i x := by
  have : h = g ∘ₗ f := LinearMap.ext fun x => (hh x).symm
  rw [this, F.map_comp A B C f g hA hB hC hf hg]; rfl

theorem map_zero' (F : DFun R n G) {A B : Ob k G} (hA : F.Obj A) (hB : F.Obj B) (i : ZMod n) (x : Vc k A.m) :
    F.map A B 0 i x = 0 := by
  have := F.map_smul A B 0 0 hA hB (fun g x => by simp) i x
  simpa using this

theorem model_sup : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N N' : Lats k n A.m), M.Model A N → M.Model A N' → M.Model A (fun i => N i ⊔ N' i) := by
  intro k G _ _ l n _ _ _ R F r Dt M A N N' hN hN'
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨B', Nb', A₂, j', p', hB', hj', hji', hp', hps', rfl⟩ := hN'
  obtain ⟨C, i, i', hi, hi', hb, hC⟩ := M.base_sum B Nb B' Nb' hB hB'
  obtain ⟨π, π', hπ, hπ', e1, e2, e3, e4, -⟩ := exists_proj hi hi' hb
  obtain ⟨S, a, a', ha, ha', hab⟩ := exists_sum A₁ A₂
  obtain ⟨q, q', hq, hq', d1, d2, d3, d4, d5⟩ := exists_proj ha ha' hab
  have oB := M.base_obj _ _ hB
  have oB' := M.base_obj _ _ hB'
  have oC := M.base_obj _ _ hC
  have o1 := F.obj_sub _ _ _ hj hji oB
  have o2 := F.obj_sub _ _ _ hj' hji' oB'
  have oS := F.obj_sum _ _ _ _ _ ha ha' hab.2 o1 o2
  have oA := F.obj_quot _ _ _ hp hps o1
  have hJ : IsHom S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') :=
    isHom_add (isHom_comp (isHom_comp hq hj) hi) (isHom_comp (isHom_comp hq' hj') hi')
  have hP : IsHom S A (p ∘ₗ q + p' ∘ₗ q') := isHom_add (isHom_comp hq hp) (isHom_comp hq' hp')
  refine ⟨C, _, S, _, _, hC, hJ, ?_, hP, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := congrArg π hx
    have h2 := congrArg π' hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add (f := _), e1, e2, e3, e4, map_zero, add_zero,
      zero_add] at h1 h2
    have h1' : q x = 0 := hji (by simpa using h1)
    have h2' : q' x = 0 := hji' (by simpa using h2)
    rw [← d5 x, h1', h2']; simp
  · intro y
    obtain ⟨x, rfl⟩ := hps y
    exact ⟨a x, by simp [d1, d3]⟩
  · funext t
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₁ S a t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₁ S a t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i ∘ₗ j) o1 oS oC ha hJ (fun x => by simp [d1, d3]),
            ← map_comp_apply F o1 oB oC hj hi (fun _ => rfl)]
          exact Submodule.mem_sup_left ⟨_, hy, rfl⟩
        · exact map_comp_apply F o1 oS oA ha hP (fun x => by simp [d1, d3]) t y
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨F.map A₂ S a' t y, ?_, ?_⟩
        · change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t (F.map A₂ S a' t y) ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t
          rw [map_comp_apply F (h := i' ∘ₗ j') o2 oS oC ha' hJ (fun x => by simp [d2, d4]),
            ← map_comp_apply F o2 oB' oC hj' hi' (fun _ => rfl)]
          exact Submodule.mem_sup_right ⟨_, hy, rfl⟩
        · exact map_comp_apply F o2 oS oA ha' hP (fun x => by simp [d2, d4]) t y
    · rintro _ ⟨s, hs, rfl⟩
      change F.map S C (i ∘ₗ j ∘ₗ q + i' ∘ₗ j' ∘ₗ q') t s ∈ F.push B C i Nb t ⊔ F.push B' C i' Nb' t at hs
      obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨u', hu', rfl⟩, h⟩ := Submodule.mem_sup.1 hs
      change F.map B C i t u + F.map B' C i' t u' = _ at h
      have h1 := congrArg (F.map C B π t) h
      have h2 := congrArg (F.map C B' π' t) h
      rw [map_add (f := _), map_comp_apply F (h := LinearMap.id) oB oC oB hi hπ e1,
        map_comp_apply F (h := 0) oB' oC oB hi' hπ e2, F.map_id B oB, map_zero' F oB' oB,
        map_comp_apply F (h := j ∘ₗ q) oS oC oB hJ hπ (fun x => by simp [e1, e2]),
        ← map_comp_apply F oS o1 oB hq hj (fun _ => rfl), add_zero, LinearMap.id_apply] at h1
      rw [map_add (f := _), map_comp_apply F (h := LinearMap.id) oB' oC oB' hi' hπ' e4,
        map_comp_apply F (h := 0) oB oC oB' hi hπ' e3, F.map_id B' oB', map_zero' F oB oB',
        map_comp_apply F (h := j' ∘ₗ q') oS oC oB' hJ hπ' (fun x => by simp [e3, e4]),
        ← map_comp_apply F oS o2 oB' hq' hj' (fun _ => rfl), zero_add, LinearMap.id_apply] at h2
      change F.map S A _ t s ∈ _
      rw [F.map_add S A _ _ oS oA (isHom_comp hq hp) (isHom_comp hq' hp'),
        ← map_comp_apply F oS o1 oA hq hp (fun _ => rfl), ← map_comp_apply F oS o2 oA hq' hp' (fun _ => rfl)]
      refine Submodule.add_mem_sup ⟨_, ?_, rfl⟩ ⟨_, ?_, rfl⟩
      · change F.map A₁ B j t _ ∈ Nb t
        rw [← h1]; exact hu
      · change F.map A₂ B' j' t _ ∈ Nb' t
        rw [← h2]; exact hu'

end GlobalTheory.Models.SupModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusion
section
noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.CloseTw
open GlobalTheory.PhiGam.Close

theorem main : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (h : ZMod n → ℕ) (w : ZMod n → ℤ) (N₁ N₂ : Lats k n m), (∀ i, IsLat (N₁ i)) → (∀ i, IsLat (N₂ i)) → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₁ → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₂ → ∀ i, sh (sg l h i) (N₁ i) ≤ N₂ i := by
  intro k _ l n m hl _ _ R D h w N₁ N₂ h₁ h₂ c₁ c₂ i
  classical
  have hex : ∀ i, ∃ a : ℕ, ∀ x ∈ N₁ i, vv k ^ a • x ∈ N₂ i := fun i => exists_pow (h₁ i).1 (h₂ i).2
  have hrec : ∀ i, Nat.find (hex (i - 1)) ≤ (Nat.find (hex i) + h i) / l := by
    intro i
    refine Nat.find_min' _ fun x hx => ?_
    refine key hl.out.pos R (D.φ i) (D.φ_semi i) (D.etale i) _ (h₂ _) _ x ?_
    have e1 : vv k ^ (w i) • D.φ i x ∈ N₁ i := by
      have := mem_sh_iff_smul_mem.1 ((c₁ i).1 (Submodule.subset_span ⟨x, hx, rfl⟩))
      rwa [neg_neg] at this
    have e2 := (c₂ i).2 (mem_sh_iff_exists.2 ⟨_, Nat.find_spec (hex i) _ e1, rfl⟩)
    have hv := vv_ne_zero k
    rw [smul_smul, smul_smul, ← zpow_natCast, ← zpow_add₀ hv, ← zpow_add₀ hv] at e2
    rw [← zpow_natCast]
    convert e2 using 3
    push_cast
    ring
  have hle := le_sg hl.out.one_lt h (fun i => Nat.find (hex i)) (fun i => by
    have := hrec (i + 1)
    simp only [add_sub_cancel_right] at this
    exact (Nat.mul_le_mul_left l this).trans (Nat.mul_div_le _ _)) i
  exact sh_le fun x hx => pow_smul_mem hle (Nat.find_spec (hex i) x hx)

end GlobalTheory.PhiGam.CloseTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolyApproxOfDenseRange
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem continuous_aeval_comp {Γ k : Type} [TopologicalSpace Γ] [CommRing k] [TopologicalSpace k]
    [IsTopologicalRing k] (f : Γ → k) (hf : Continuous f) (P : MvPolynomial Γ ℤ) :
    Continuous fun u : Γ → Γ => MvPolynomial.aeval (f ∘ u) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, Function.comp_apply]
    exact hp.mul (hf.comp (continuous_apply j))

theorem polyApprox_of_denseRange : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ), DenseRange x → ∀ (T : Γ → PadicAlgCl l), Continuous T →
    ∀ (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) →
    PolyApprox (fun j => T (x j)) ((fun ρ j => trc ρ (x j)) '' C) → PolyApprox T (trc '' C) := by
  intro l _ Γ _ _ _ _ a J x hx T hT C hC h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  have hch : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η := fun η hη => hs hη
  choose! ρ hρC hρη using hch
  have inj : Set.InjOn (fun η => trc (ρ η)) (s : Set (J → PadicAlgCl l)) := by
    intro η₁ h₁ η₂ h₂ e
    rw [← hρη η₁ h₁, ← hρη η₂ h₂]
    simp only at e
    rw [e]
  refine ⟨s.image (fun η => trc (ρ η)), fun σ => c (fun j => σ (x j)), ?_, fun P => ?_⟩
  · intro σ hσ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hσ
    obtain ⟨η, hη, rfl⟩ := hσ
    exact ⟨ρ η, hρC η hη, rfl⟩
  rw [Finset.sum_image inj]
  have hc : ∀ η ∈ s, c (fun j => trc (ρ η) (x j)) = c η := fun η hη => by rw [hρη η hη]
  rw [Finset.sum_congr rfl (fun η hη => by rw [show (fun σ : Γ → PadicAlgCl l => c fun j => σ (x j)) (trc (ρ η)) = c η from hc η hη])]
  have htr : ∀ η ∈ s, Continuous (trc (ρ η)) := fun η hη =>
    (Units.continuous_val.comp (hC _ (hρC η hη))).matrix_trace
  let F : (Γ → Γ) → PadicAlgCl l := fun u =>
    MvPolynomial.aeval (T ∘ u) P - ∑ η ∈ s, c η * MvPolynomial.aeval (trc (ρ η) ∘ u) P
  have hF : Continuous F := by
    refine (continuous_aeval_comp T hT P).sub (continuous_finsetSum _ fun η hη => ?_)
    exact continuous_const.mul (continuous_aeval_comp _ (htr η hη) P)
  have key : ‖F id‖ ≤ ε := by
    refine (DenseRange.piMap (fun _ : Γ => hx)).induction_on (p := fun u => ‖F u‖ ≤ ε) id
      (isClosed_le (continuous_norm.comp hF) continuous_const) fun v => ?_
    have e1 : MvPolynomial.aeval (T ∘ Pi.map (fun _ : Γ => x) v) P =
        MvPolynomial.aeval (fun j => T (x j)) (MvPolynomial.rename v P) := by
      rw [MvPolynomial.aeval_rename]; rfl
    have e2 : ∀ η ∈ s, MvPolynomial.aeval (trc (ρ η) ∘ Pi.map (fun _ : Γ => x) v) P =
        MvPolynomial.aeval η (MvPolynomial.rename v P) := fun η hη => by
      have e3 : trc (ρ η) ∘ Pi.map (fun _ : Γ => x) v = η ∘ v := by
        funext i
        simp only [Function.comp_apply, Pi.map_apply]
        exact congrFun (hρη η hη) (v i)
      rw [MvPolynomial.aeval_rename, e3]
    have := hP (MvPolynomial.rename v P)
    simp only [F]
    rw [e1, Finset.sum_congr rfl (fun η hη => by rw [e2 η hη])]
    exact this
  exact key

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanIsLinesOfGraded
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

namespace GlobalTheory.SenLines.SplitFil

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def lineMap {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) : (Fin r → F⟦X⟧) →ₗ[F] (ℤ → M) where
  toFun c := ∑ k, serLine (u k) (d k) (c k)
  map_add' c c' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext m
    simp only [serLine, Pi.add_apply]
    split_ifs <;> simp [add_smul]
  map_smul' a c := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext m
    simp only [serLine, Pi.smul_apply]
    split_ifs <;> simp [mul_smul]

theorem smul_serMul (a : F) (f : F⟦X⟧) {y : ℤ → M} (hy : IsLaurent y) :
    a • serMul f y = serMul (a • f) y := by
  funext m
  simp only [Pi.smul_apply, serMul]
  rw [smul_finsum' a (serMul_finite f hy m)]
  refine finsum_congr fun j => ?_
  simp [mul_smul]

theorem mem_serSpan_iff {N : Type} (L : N → ℤ → M) (hL : ∀ x, IsLaurent (L x)) (y : ℤ → M) :
    y ∈ serSpan F (Set.range L) ↔
      ∃ (s : ℕ) (x : Fin s → N) (f : Fin s → F⟦X⟧), y = ∑ j, serAct (f j) (L (x j)) := by
  constructor
  · intro hy
    obtain ⟨n, c, g, h⟩ := Submodule.mem_span_set'.mp hy
    have hg : ∀ i, ∃ (f : F⟦X⟧) (x : N), (g i : ℤ → M) = serMul f (L x) := fun i => by
      obtain ⟨f, w, ⟨x, rfl⟩, -, h⟩ := (g i).2
      exact ⟨f, x, h⟩
    choose f x hg using hg
    refine ⟨n, x, fun i => c i • f i, ?_⟩
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg, smul_serMul _ _ (hL _)]
    rfl
  · rintro ⟨s, x, f, rfl⟩
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.subset_span ⟨f j, L (x j), ⟨x j, rfl⟩, hL _, rfl⟩

theorem exists_coef {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (a : ℤ) (z : M)
    (hz : z ∈ Submodule.span F (d '' {k | a ≤ u k})) :
    ∃ c : Fin r → F, (∀ k, u k < a → c k = 0) ∧ z = ∑ k, c k • d k := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun k' hk' => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hk (not_le.mpr hk')
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨c', hc', rfl⟩ := hy
    exact ⟨c + c', fun k hk => by simp [hc k hk, hc' k hk],
      by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul b x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨b • c, fun k hk => by simp [hc k hk], by simp [mul_smul, Finset.smul_sum]⟩

theorem gradedSer_eq_range {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (A : ℤ → Submodule F M)
    (hA : ∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) :
    gradedSer A = LinearMap.range (lineMap (F := F) u d) := by
  apply le_antisymm
  · refine iSup_le fun a y hy => ?_
    obtain ⟨hy0, hy1⟩ := hy
    have hex : ∀ m : ℤ, ∃ c : Fin r → F, (∀ k, m + u k < 0 → c k = 0) ∧
        y m = ∑ k, c k • d k := fun m => by
      by_cases hm : m < -a
      · exact ⟨0, fun _ _ => rfl, by simp [hy0 m hm]⟩
      · obtain ⟨c, hc, h⟩ := exists_coef u d a (y m) (hA a ▸ hy1 m)
        exact ⟨c, fun k hk => hc k (by omega), h⟩
    choose c hc hyc using hex
    refine ⟨fun k => PowerSeries.mk fun j => c ((j : ℤ) - u k) k, ?_⟩
    funext m
    change (∑ k, serLine (u k) (d k) (PowerSeries.mk fun j => c ((j : ℤ) - u k) k)) m = y m
    rw [Finset.sum_apply, hyc]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold serLine
    split_ifs with h
    · rw [coeff_mk, Int.toNat_of_nonneg h, add_sub_cancel_right]
    · rw [hc m k (not_le.mp h), zero_smul]
  · rintro _ ⟨c, rfl⟩
    change (∑ k, serLine (u k) (d k) (c k)) ∈ _
    refine Submodule.sum_mem _ fun k _ => ?_
    refine Submodule.mem_iSup_of_mem (u k) ⟨fun m hm => ?_, fun m => ?_⟩
    · unfold serLine
      rw [if_neg (by omega)]
    · unfold serLine
      split_ifs
      · rw [hA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, le_refl (u k), rfl⟩)
      · exact Submodule.zero_mem _

theorem spanIsLines_of_graded : ∀ {F M N : Type} [Field F] [AddCommGroup M] [Module F M] (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (A : ℤ → Submodule F M), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent (L x)) → (∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) → GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serSpan F (Set.range L) = GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.gradedSer A → GlobalTheory.SenLines.SpanIsLines L u d F := by
  intro F M N _ _ _ L r u d A hL hA h y
  rw [← mem_serSpan_iff L hL, h, gradedSer_eq_range u d A hA]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

end GlobalTheory.SenLines.SplitFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralSqEqOne
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem stableGauss_sq_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → G₁ ^ 2 = 1 := by
  intro F E _ _ _ _ _ A ψ x μ ω hH G₁ hG
  have hG' := _root_.GlobalTheory.JR.WeilQuad.stableGauss_neg_one F E A ψ x μ ω hH G₁ hG
  obtain ⟨Λ₀, -, hc₀, h₀⟩ := hG
  obtain ⟨Λ₁, -, hc₁, h₁⟩ := hG'
  obtain ⟨Λ, ho, hc, hsub, hperp, hV⟩ := _root_.GlobalTheory.JR.WeilQuad.LargeLattice.main F E A ψ x μ ω hH ((Λ₀ : Set A.L) ∪ Λ₁) (hc₀.union hc₁)
    _ (_root_.GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero F E A ψ x μ ω hH)
  have e0 := h₀ Λ ho hc (fun y hy => hsub (Or.inl hy))
  have e1 := h₁ Λ ho hc (fun y hy => hsub (Or.inr hy))
  have hp := _root_.GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one F E A ψ x μ ω hH Λ ho hc hperp (fun y hy => hV hy)
  rw [e0, e1] at hp
  rw [sq]; exact hp

end GlobalTheory.JR.WeilQuad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormDetOneAddSmul
section
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg

def unitBallSubring (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] : Subring E where
  carrier := {t | ‖t‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem norm_det_one_add_smul (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
    (x : Matrix (Fin n) (Fin n) E) (ϖ : E) (hϖ : ‖ϖ‖ < 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ‖(1 + ϖ • x).det‖ = 1 := by
  set O := unitBallSubring E
  let y : Matrix (Fin n) (Fin n) O := fun i j => ⟨x i j, hx i j⟩
  let w : O := ⟨ϖ, hϖ.le⟩
  have hmap : O.subtype.mapMatrix (1 + w • y) = 1 + ϖ • x := by
    rw [map_add (f := _), map_one]
    congr 1
  have hdet : (1 + ϖ • x).det = ((1 + w • y).det : E) := by
    rw [← hmap, ← RingHom.map_det]; rfl
  have hq : (Ideal.Quotient.mk (Ideal.span {w})) (1 + w • y).det = 1 := by
    rw [RingHom.map_det, map_add (f := _), map_one]
    have : (Ideal.Quotient.mk (Ideal.span {w})).mapMatrix (w • y) = 0 := by
      ext i j
      simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    rw [this, add_zero, Matrix.det_one]
  have hmem : (1 + w • y).det - 1 ∈ Ideal.span {w} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hq, map_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hc' : ((1 + w • y).det : E) - 1 = (c : E) * ϖ := by
    have := congrArg Subtype.val hc
    simpa [w] using this.symm
  have hlt : ‖(1 + ϖ • x).det - 1‖ < 1 := by
    rw [hdet, hc', norm_mul]
    calc ‖(c : E)‖ * ‖ϖ‖ ≤ 1 * ‖ϖ‖ := mul_le_mul_of_nonneg_right c.2 (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hϖ
  have key : (1 + ϖ • x).det = 1 + ((1 + ϖ • x).det - 1) := by ring
  rw [key, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne')]
  simp [hlt.le]

end GlobalTheory.UnitDiscAlg
end

