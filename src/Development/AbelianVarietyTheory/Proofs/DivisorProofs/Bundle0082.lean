module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIsotropicLiftModIdeal
section
namespace GlobalTheory

theorem isotropic_summand_lift : ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Type) [AddCommGroup D] [Module R D] [Module.Finite R D] [Module.Projective R D] (φ : D →ₗ[R] D →ₗ[R] R), I ^ 2 = ⊥ → IsUnit (2 : R) → (∀ x y, φ x y = -φ y x) → (∀ l : D →ₗ[R] R, ∃ z, ∀ x, l x - φ x z ∈ I) → ∀ F N : Submodule R D, IsCompl F N → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → ∃ E N' : Submodule R D, IsCompl E N' ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ E ⊔ I • (⊤ : Submodule R D) = F ⊔ I • (⊤ : Submodule R D) := by
  intro R _ I D _ _ _ _ φ hI2 h2 hskew hsurj F N hFN hF
  have hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := by
    intro a ha b hb
    have h : a * b ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hI2] at h; exact (Submodule.mem_bot R).1 h
  have hφI : ∀ a ∈ I • (⊤ : Submodule R D), ∀ y, φ a y ∈ I := by
    intro a ha y
    refine Submodule.smul_induction_on (p := fun a => φ a y ∈ I) ha ?_ ?_
    · intro r hr m _
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro x z hx hz
      simp only [map_add (f := _), LinearMap.add_apply]
      exact I.add_mem hx hz
  have hφII : ∀ a ∈ I • (⊤ : Submodule R D), ∀ b ∈ I • (⊤ : Submodule R D), φ a b = 0 := by
    intro a ha b hb
    refine Submodule.smul_induction_on (p := fun a => φ a b = 0) ha ?_ ?_
    · intro r hr m _
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      have : φ m b ∈ I := by rw [hskew]; exact I.neg_mem (hφI b hb m)
      exact hII r hr _ this
    · intro x z hx hz
      simp only [map_add (f := _), LinearMap.add_apply, hx, hz, add_zero]
  have hsmul0 : ∀ r ∈ I, ∀ w ∈ I • (⊤ : Submodule R D), r • w = 0 := by
    intro r hr w hw
    refine Submodule.smul_induction_on (p := fun w => r • w = 0) hw ?_ ?_
    · intro r' hr' m _
      rw [smul_smul, hII r hr r' hr', zero_smul]
    · intro x z hx hz
      rw [smul_add, hx, hz, add_zero]

  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R D
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfs : ∀ x, f (s x) = x := fun x => by simpa using LinearMap.congr_fun hs x
  let e : Fin n → D := fun i => f (fun j => if i = j then 1 else 0)
  have hexp : ∀ x, x = ∑ i, s x i • e i := fun x => by
    conv_lhs => rw [← hfs x]
    exact LinearMap.pi_apply_eq_sum_univ f (s x)
  choose z hz using fun i : Fin n => hsurj ((LinearMap.proj i).comp s)
  have hz' : ∀ i x, s x i - φ x (z i) ∈ I := fun i x => by simpa using hz i x

  let P : D →ₗ[R] D := F.subtype ∘ₗ Submodule.linearProjOfIsCompl F N hFN
  have hPF : ∀ x, P x ∈ F := fun x => (Submodule.linearProjOfIsCompl F N hFN x).2
  have hPx : ∀ x ∈ F, P x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hFN ⟨x, hx⟩)
  let B : D →ₗ[R] D →ₗ[R] R := φ.compl₁₂ P P
  have hB : ∀ x y, B x y = φ (P x) (P y) := fun x y => rfl
  have hBI : ∀ x y, B x y ∈ I := fun x y => hF _ (hPF x) _ (hPF y)
  let c : R := ↑(h2.unit⁻¹)
  have hc : c * 2 = 1 := h2.val_inv_mul
  let T : D →ₗ[R] D := ∑ i, (-c) • (LinearMap.smulRight (B (e i)) (z i))
  have hT : ∀ y, T y = ∑ i, (-c) • (B (e i) y • z i) := fun y => by
    simp [T]
  have hTr : ∀ y, T y ∈ I • (⊤ : Submodule R D) := fun y => by
    rw [hT]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.smul_mem_smul (hBI _ _) Submodule.mem_top)
  have hTI : ∀ a ∈ I • (⊤ : Submodule R D), T a = 0 := by
    intro a ha
    refine Submodule.smul_induction_on (p := fun a => T a = 0) ha ?_ ?_
    · intro r hr m _
      rw [map_smul]; exact hsmul0 r hr _ (hTr m)
    · intro x w hx hw
      rw [map_add (f := _), hx, hw, add_zero]
  have hTT : ∀ y, T (T y) = 0 := fun y => hTI _ (hTr y)
  have hkey0 : ∀ x y, φ x (T y) = -c * B x y := by
    intro x y
    have hBx : B x y = ∑ i, s x i * B (e i) y := by
      conv_lhs => rw [hexp x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, LinearMap.sum_apply, smul_eq_mul]
    have h0 : ∑ i, B (e i) y * (s x i - φ x (z i)) = 0 :=
      Finset.sum_eq_zero fun i _ => hII _ (hBI _ _) _ (hz' i x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, map_sum, hBx]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    have h1 : ∑ i, -c * (s x i * B (e i) y) - ∑ i, -c * (B (e i) y * φ x (z i)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      have : ∀ i, -c * (s x i * B (e i) y) - -c * (B (e i) y * φ x (z i))
          = -c * (B (e i) y * (s x i - φ x (z i))) := fun i => by ring
      simp only [this]
      rw [← Finset.mul_sum, h0, mul_zero]
    exact (sub_eq_zero.1 h1).symm
  have hkey : ∀ x ∈ F, ∀ y ∈ F, φ x (T y) = -c * φ x y := by
    intro x hx y hy
    rw [hkey0, hB, hPx x hx, hPx y hy]
  let u : D ≃ₗ[R] D := LinearEquiv.ofLinear (LinearMap.id + T) (LinearMap.id - T)
    (LinearMap.ext fun y => by simp [hTT]) (LinearMap.ext fun y => by simp [hTT])
  have hu : ∀ x, u x = x + T x := fun x => rfl
  refine ⟨F.map (u : D →ₗ[R] D), N.map (u : D →ₗ[R] D), ?_, ?_, ?_⟩
  · exact (Submodule.orderIsoMapComap u).isCompl hFN
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ (u x) (u y) = 0
    rw [hu, hu, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply]
    have h1 := hkey x hx y hy
    have h2' := hkey y hy x hx
    have h3 := hskew (T x) y
    have h4 := hskew y x
    have h5 := hφII (T x) (hTr x) (T y) (hTr y)
    linear_combination h1 + h3 - h2' + h5 + c * h4 - (φ x y) * hc
  · apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨x, hx, rfl⟩
      show u x ∈ _
      rw [hu]
      exact Submodule.add_mem_sup hx (hTr x)
    · refine sup_le ?_ le_sup_right
      intro x hx
      refine Submodule.mem_sup.2 ⟨u x, ⟨x, hx, rfl⟩, -T x, Submodule.neg_mem _ (hTr x), ?_⟩
      rw [hu]; abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
section
noncomputable section

namespace GlobalTheory.LatOrb

open Polynomial Matrix

variable (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K]

def stdLat (n : ℕ) : Submodule O (Fin n → K) where
  carrier := {v | ∀ i, v i ∈ (algebraMap O K).range}
  add_mem' := by
    intro a b ha hb i
    exact Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun i => Subring.zero_mem _
  smul_mem' := by
    intro c v hv i
    obtain ⟨a, ha⟩ := hv i
    exact ⟨c * a, by simp [Algebra.smul_def, ha]⟩

def matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    Submodule O (Fin n → K) :=
  M.map ((Matrix.mulVecLin g).restrictScalars O)

def IsLatV {n : ℕ} (M : Submodule O (Fin n → K)) : Prop :=
  M.FG ∧ Submodule.span K (M : Set (Fin n → K)) = ⊤

def herm {n : ℕ} (σ : K →+* K) (x y : Fin n → K) : K := ∑ k, x k * σ (y k)

def SelfDual {n : ℕ} (σ : K →+* K) (M : Submodule O (Fin n → K)) : Prop :=
  ∀ y, y ∈ M ↔ ∀ x ∈ M, herm σ y x ∈ (algebraMap O K).range

variable {O}

theorem mem_stdLat {n : ℕ} (v : Fin n → K) : v ∈ stdLat O n ↔ ∀ i, v i ∈ (algebraMap O K).range :=
  Iff.rfl

theorem mem_matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K))
    (v : Fin n → K) : v ∈ matLat O g M ↔ ∃ u ∈ M, g *ᵥ u = v := by
  simp [matLat]

theorem matLat_mul {n : ℕ} (a b : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    matLat O (a * b) M = matLat O a (matLat O b M) := by
  ext v
  simp only [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨b *ᵥ u, ⟨u, hu, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [Matrix.mulVec_mulVec]⟩

theorem matLat_one {n : ℕ} (M : Submodule O (Fin n → K)) : matLat O 1 M = M := by
  ext v
  simp [mem_matLat]

end GlobalTheory.LatOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfIrred
section
universe u v

namespace GlobalTheory.CompanionTheory.BurnsideU

theorem mem_of_irred {K : Type u} {V : Type v} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf : f = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf]
    exact S.zero_mem

  have : IsScalarTower K S V := ⟨fun _ _ _ => rfl⟩
  have : Nontrivial (Submodule S V) := (Submodule.nontrivial_iff S).mpr hV

  have : IsSimpleModule S V :=
    { eq_bot_or_eq_top := fun N => by
        rcases hirr (N.restrictScalars K) (fun g hg v hv => N.smul_mem ⟨g, hg⟩ hv) with h | h
        · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff K S V).mp h)
        · exact Or.inr ((Submodule.restrictScalars_eq_top_iff K S V).mp h) }

  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K

  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g v => by
        obtain ⟨c, rfl⟩ := hschur.2 g
        change f ((algebraMap K (Module.End S V) c) v) = (algebraMap K (Module.End S V) c) (f v)
        simp [Module.algebraMap_end_apply, f.map_smul] }

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := V)
  obtain ⟨r, hr⟩ := jacobson_density F s
  have hfr : f = (r : Module.End K V) := by
    apply LinearMap.ext
    intro m
    have hm : m ∈ Submodule.span K (s : Set V) := hs ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => exact hr m hm
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add (f := _), map_add (f := _), h₁, h₂]
    | smul c _ _ h => rw [map_smul, map_smul, h]
  rw [hfr]
  exact r.2

theorem burnside_surj_of_irred {A : Type u} {V : Type v} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ :=
    by
    intro f
    have hf : f ∈ ρ.range :=
      mem_of_irred ρ.range (fun W hW => hirr W fun h w hw => hW (ρ h) ⟨h, rfl⟩ w hw) f
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range ρ).mp hf
    exact ⟨h, rfl⟩

end GlobalTheory.CompanionTheory.BurnsideU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfIrreducible
section
universe u_1 u_2

namespace GlobalTheory.IrreducibleMembership

theorem mem_of_irreducible {K : Type u_1} {V : Type u_2} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf1 : f = 1 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf1]
    exact S.one_mem
  · have hso : IsSimpleOrder (Submodule S V) := by
      refine ⟨fun N => ?_⟩
      have hN := h (N.restrictScalars K) fun g hg v hv => by
        have hmem : (⟨g, hg⟩ : S) • v ∈ N := N.smul_mem _ hv
        exact hmem
      rcases hN with hN | hN
      · left
        exact (Submodule.restrictScalars_eq_bot_iff K S V).1 hN
      · right
        exact (Submodule.restrictScalars_eq_top_iff K S V).1 hN
    have hsimp : IsSimpleModule S V := ⟨⟩
    have hbij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K
    let F : Module.End (Module.End S V) V :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun g v => by
          obtain ⟨c, hc⟩ := hbij.2 g
          rw [← hc]
          simp }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
    have hfr : f = (r : Module.End K V) := by
      refine b.ext fun i => ?_
      have := hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
      exact this
    rw [hfr]
    exact r.2

end GlobalTheory.IrreducibleMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfMemSpanRingOfIntegersMapNumberField
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FlatDescent

theorem mem_of_mem_span_of_isBaseChange {A B M M' : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [Module B M'] [IsScalarTower A B M'] {f : M →ₗ[A] M'} (hf : IsBaseChange B f)
    (N : Submodule A M) (w : M) (hw : f w ∈ Submodule.span B (f '' (N : Set M))) : w ∈ N := by
  let g : B ⊗[A] N →ₗ[B] M' := hf.equiv.toLinearMap ∘ₗ N.subtype.baseChange B
  have hspan : Submodule.span B (f '' (N : Set M)) ≤ LinearMap.range g := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨(1 : B) ⊗ₜ[A] (⟨c, hc⟩ : N), by simp [g, IsBaseChange.equiv_tmul]⟩
  obtain ⟨x, hx⟩ := hspan hw
  have h1 : (1 : B) ⊗ₜ[A] w = N.subtype.baseChange B x := by
    apply hf.equiv.injective
    have : hf.equiv (N.subtype.baseChange B x) = f w := hx
    rw [this, IsBaseChange.equiv_tmul, one_smul]
  have hq : N.mkQ ∘ₗ N.subtype = 0 := by
    ext c
    simp
  have h2 : (1 : B) ⊗ₜ[A] (N.mkQ w) = 0 := by
    have := congrArg (N.mkQ.baseChange B) h1
    rw [LinearMap.baseChange_tmul] at this
    rw [this, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hq, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
  have h3 : N.mkQ w = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) (M ⧸ N)
    simpa using h2
  simpa using h3

theorem mem_of_mem_span_map :
    ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (N : Submodule (𝓞 K) (Fin n → K)) (w : Fin n → K),
    (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin n → K) i => j (c i)) '' (N : Set (Fin n → K))) → w ∈ N := by
  intro K K' _ _ _ _ j n N w hw
  letI := j.toAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K') (nonZeroDivisors (𝓞 K))) K' :=
    IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')
  have hP : Algebra.IsPushout (𝓞 K) (𝓞 K') K K' :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 K') K'
  have hb : IsBaseChange (𝓞 K')
      ((IsScalarTower.toAlgHom (𝓞 K) K K').toLinearMap.compLeft (Fin n)) :=
    hP.out.finitePow (Fin n)
  exact mem_of_mem_span_of_isBaseChange hb N w hw

end GlobalTheory.FlatDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfSemilinearMemComplexSpan
section
namespace GlobalTheory

theorem mem_of_semilinear_mem_complex_span : ∀ {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V), LinearIndependent ℂ (fun k => j (b k)) → ∀ (U : Submodule K V) (x : V), j x ∈ Submodule.span ℂ (j '' (U : Set V)) → x ∈ U := by
  intro K V W ι _ _ _ _ _ _ σ j b hli U x hx
  by_contra hxU
  obtain ⟨f, hfx, hfU⟩ := U.exists_dual_map_eq_bot_of_notMem hxU inferInstance
  obtain ⟨L, hL⟩ := (Finsupp.linearCombination ℂ (fun k => j (b k))).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hli)
  let g : W →ₗ[ℂ] ℂ := (Finsupp.linearCombination ℂ (fun k => σ (f (b k)))).comp L
  have hb : ∀ k, g (j (b k)) = σ (f (b k)) := by
    intro k
    have h1 : L (j (b k)) = Finsupp.single k 1 := by
      have := LinearMap.congr_fun hL (Finsupp.single k 1)
      simpa using this
    simp [g, h1]
  have hg : ∀ v, g (j v) = σ (f v) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hb k
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => rw [j.map_smulₛₗ, map_smul, map_smul, hy]; simp
  have hle : Submodule.span ℂ (j '' (U : Set V)) ≤ LinearMap.ker g := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have : f u = 0 := by
      have : f u ∈ U.map f := ⟨u, hu, rfl⟩
      rw [hfU] at this
      simpa using this
    simp [hg, this]
  have h0 : σ (f x) = 0 := by rw [← hg]; exact hle hx
  exact hfx (by simpa using h0)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfSumMem
section
namespace GlobalTheory.MembershipOfSum

theorem mem_of_sum_mem {k : Type} [Field k] {H : Type 1} [AddCommGroup H] [Module k H]
    {O : Type} [CommRing O] (ρ : O →+* Module.End k H) (F : Submodule k H)
    (hF : ∀ (c : O), ∀ x ∈ F, ρ c x ∈ F) {a : ℕ} (χ : Fin a → O → k)
    (hχ : ∀ (i j : Fin a), i ≠ j → ∃ (c : O), χ i c ≠ χ j c) (S : Finset (Fin a))
    (u : Fin a → H) (hu : ∀ i ∈ S, ∀ (c : O), ρ c (u i) - χ i c • u i ∈ F)
    (hs : ∑ i ∈ S, u i ∈ F) : ∀ i ∈ S, u i ∈ F := by
  induction S using Finset.induction_on generalizing u with
  | empty => intro i hi; simp at hi
  | insert j S hj ih =>
    have key : ∀ i ∈ S, u i ∈ F := by
      intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      obtain ⟨c, hc⟩ := hχ i j hij
      have h1 : ∑ l ∈ insert j S, (χ l c - χ j c) • u l ∈ F := by
        have e : ∑ l ∈ insert j S, (χ l c - χ j c) • u l =
            ρ c (∑ l ∈ insert j S, u l) - χ j c • ∑ l ∈ insert j S, u l
              - ∑ l ∈ insert j S, (ρ c (u l) - χ l c • u l) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [sub_smul]; abel
        rw [e]
        exact F.sub_mem (F.sub_mem (hF c _ hs) (F.smul_mem _ hs))
          (F.sum_mem fun l hl => hu l hl c)
      rw [Finset.sum_insert hj, sub_self, zero_smul, zero_add] at h1
      have h2 := ih (fun l => (χ l c - χ j c) • u l) (by
        intro l hl d
        have := F.smul_mem (χ l c - χ j c) (hu l (Finset.mem_insert_of_mem hl) d)
        rw [smul_sub, smul_comm] at this
        rw [map_smul]
        exact this) h1 i hi
      exact (F.smul_mem_iff (sub_ne_zero.mpr hc)).mp h2
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_insert hj] at hs
      have := F.sub_mem hs (F.sum_mem key)
      simpa using this
    · exact key i hi

end GlobalTheory.MembershipOfSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat

variable {E : Type} [Field E] [NumberField E]

def scLat {n : ℕ} (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ}
  zero_mem' := fun c _ => by rw [smul_zero]; exact Λ.zero_mem
  add_mem' := fun hx hy c hc => by rw [smul_add]; exact Λ.add_mem (hx c hc) (hy c hc)
  smul_mem' := fun r y hy c hc => by rw [smul_comm]; exact Λ.smul_mem r (hy c hc)

theorem mem_scLat {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {Λ : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} :
    y ∈ scLat 𝔞 Λ ↔ ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ := Iff.rfl

def blkA {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin a → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inl)

def blkB {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin b → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inr)

def pairLat {a b d : ℕ} (ΛA : Submodule (𝓞 E) (Fin a → E)) (ΛB : Submodule (𝓞 E) (Fin b → E))
    (e : Fin a ⊕ Fin b ≃ Fin d) : Submodule (𝓞 E) (Fin d → E) :=
  ΛA.comap (blkA e) ⊓ ΛB.comap (blkB e)

theorem mem_pairLat {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}
    {e : Fin a ⊕ Fin b ≃ Fin d} {x : Fin d → E} :
    x ∈ pairLat ΛA ΛB e ↔ (fun k => x (e (.inl k))) ∈ ΛA ∧ (fun k => x (e (.inr k))) ∈ ΛB := Iff.rfl

end GlobalTheory.SkewLat

end
end

