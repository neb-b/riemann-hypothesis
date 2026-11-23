module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOfPair

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.ExistsIntegralMultiple
section
noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem scale_E (L : LocE F E) (y : E) :
    ∃ r : 𝒪[F], (r : F) ≠ 0 ∧ algebraMap F E r * y ∈ L.O := by
  obtain ⟨T, hT⟩ := SlopeTestRemainingChoices.tr_ex L y
  obtain ⟨N, hN⟩ := SlopeTestRemainingChoices.nm_ex L y
  obtain ⟨r₁, h10, h1⟩ := SlopeTestRemainingChoices.exists_scale T
  obtain ⟨r₂, h20, h2⟩ := SlopeTestRemainingChoices.exists_scale N
  obtain ⟨r, hr⟩ : ∃ r : 𝒪[F], (r : F) = (r₁ : F) * (r₂ : F) := ⟨r₁ * r₂, rfl⟩
  refine ⟨r, by rw [hr]; exact mul_ne_zero h10 h20, ?_⟩
  refine SlopeTestRemainingChoices.mem_O_of_quad L _ ⟨(r : F) * T, ?_⟩ ⟨(r : F) * (r : F) * N, ?_⟩ ?_
  · have : (r : F) * T = (r₂ : F) * ((r₁ : F) * T) := by rw [hr]; ring
    rw [this]; exact (𝒪[F]).mul_mem r₂.2 h1
  · have : (r : F) * (r : F) * N = ((r₁ : F) * (r₁ : F) * (r₂ : F)) * ((r₂ : F) * N) := by
      rw [hr]; ring
    rw [this]; exact (𝒪[F]).mul_mem ((𝒪[F]).mul_mem ((𝒪[F]).mul_mem r₁.2 r₁.2) r₂.2) h2
  · simp only [map_mul, hT, hN]
    ring

end

theorem existsIntegralMultiple : Scale := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ S w hw
  have key : ∀ (r : 𝒪[F]) (v : V), v ∈ S → algebraMap F E r • v ∈ S := by
    intro r v hv
    have : (⟨algebraMap F E r, SlopeTestRemainingChoices.algebraMap_mem_O M.L r⟩ : M.L.O) • v ∈ S := S.smul_mem _ hv
    exact this
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, by simp, by simpa using hx⟩
  | zero => exact ⟨1, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr0, hr⟩ := hx
    obtain ⟨s, hs0, hs⟩ := hy
    obtain ⟨t, ht⟩ : ∃ t : 𝒪[F], (t : F) = (r : F) * (s : F) := ⟨r * s, rfl⟩
    refine ⟨t, by rw [ht]; exact mul_ne_zero hr0 hs0, ?_⟩
    have e : algebraMap F E t • (x + y) =
        algebraMap F E s • (algebraMap F E r • x) + algebraMap F E r • (algebraMap F E s • y) := by
      rw [ht, smul_add, smul_smul, smul_smul, map_mul, mul_comm (algebraMap F E s)]
    rw [e]
    exact S.add_mem (key s _ hr) (key r _ hs)
  | smul a x _ hx =>
    obtain ⟨r, hr0, hr⟩ := hx
    obtain ⟨s, hs0, hs⟩ := scale_E M.L a
    obtain ⟨t, ht⟩ : ∃ t : 𝒪[F], (t : F) = (s : F) * (r : F) := ⟨s * r, rfl⟩
    refine ⟨t, by rw [ht]; exact mul_ne_zero hs0 hr0, ?_⟩
    have e : algebraMap F E t • (a • x) =
        (⟨algebraMap F E s * a, hs⟩ : M.L.O) • (algebraMap F E r • x) := by
      change _ = (algebraMap F E s * a) • (algebraMap F E r • x)
      rw [ht, smul_smul, smul_smul, map_mul]
      ring_nf
    rw [e]
    exact S.smul_mem _ hr

end PI.LocHerm.Glue
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.MemOfProjEqZero
section
noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

section Basic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, ← neg_one_smul E x', H.h_add_left, H.h_smul_left]
  ring

theorem h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm, ← H.h_herm]

def hlin (u : V) : V →ₗ[E] E where
  toFun v := H.h v u
  map_add' a b := H.h_add_left a b u
  map_smul' a v := by rw [H.h_smul_left]; rfl

end Basic

section Proj

variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V]

theorem sub_proj_mem {A B : Submodule E V} (hAB : IsCompl A B) (x : V) :
    x - (A.projectionOnto B hAB x : V) ∈ B := by
  rw [← Submodule.projectionOnto_apply_eq_zero_iff hAB, map_sub,
    Submodule.projectionOnto_apply_left, sub_self]

theorem mem_of_proj_eq_zero {A B : Submodule E V} (hAB : IsCompl A B) {x : V}
    (h : (A.projectionOnto B hAB x : V) = 0) : x ∈ B := by
  exact (Submodule.projectionOnto_apply_eq_zero_iff hAB).1 (Subtype.ext h)

end Proj

set_option linter.deprecated false in
theorem pair_of (hR : Riesz) (hS : Scale) (hO : PI.LocHerm.LocOProj) : Pair := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H abelian₂ hL A B hAB orth u hu
  have e : Submodule.linearProjOfIsCompl A B hAB = A.projectionOnto B hAB := rfl
  rw [e]
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy hyA
    have hxB := sub_proj_mem hAB x
    have h1 : H.h x y = H.h (A.projectionOnto B hAB x : V) y := by
      have e2 := H.h_add_left (A.projectionOnto B hAB x : V) (x - (A.projectionOnto B hAB x : V)) y
      rw [add_sub_cancel, (orth y hyA _ hxB).2, add_zero] at e2
      exact e2
    rw [← h1]
    exact (hL.2.2 x).1 hx y hy
  · intro hyp

    let pB : V →ₗ[E] V := B.subtype ∘ₗ B.projectionOnto A hAB.symm
    have pB_apply : ∀ v, pB v = (B.projectionOnto A hAB.symm v : V) := fun v => rfl
    let P : Submodule M.L.O V := abelian₂.map (pB.restrictScalars M.L.O)
    let π : abelian₂ →ₗ[M.L.O] P := (pB.restrictScalars M.L.O).submoduleMap abelian₂
    have hπ : Function.Surjective π := LinearMap.submoduleMap_surjective _ _
    have hπv : ∀ l : abelian₂, (π l : V) = pB l := fun l => rfl
    have hPfg : P.FG := hL.1.map _
    have : Module.Projective M.L.O P := hO F E M hM V P hPfg
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    have hsp : ∀ p : P, pB (s p : V) = p := by
      intro p
      have := congrArg Subtype.val (LinearMap.congr_fun hs p)
      rw [← hπv]
      exact this
    let Q : Submodule M.L.O V := LinearMap.range (abelian₂.subtype ∘ₗ s)
    let W : Submodule E V := Submodule.span E (Q : Set V)
    have hsW : ∀ p : P, (s p : V) ∈ W := fun p => Submodule.subset_span ⟨p, rfl⟩

    let d : abelian₂ → V := fun l => (l : V) - s (π l)
    have hdA : ∀ l : abelian₂, d l ∈ A := by
      intro l
      apply mem_of_proj_eq_zero hAB.symm
      rw [← pB_apply, map_sub, hsp, hπv, sub_self]
    have hdL : ∀ l : abelian₂, d l ∈ abelian₂ := fun l => abelian₂.sub_mem l.2 (s (π l)).2
    have hcompl : IsCompl A W := by
      refine isCompl_iff.2 ⟨?_, codisjoint_iff.2 ?_⟩
      · rw [Submodule.disjoint_def]
        intro w hwA hwW
        obtain ⟨r, hr0, hrw⟩ := hS M hM V Q w hwW
        obtain ⟨p, hp⟩ := hrw
        have hp' : (s p : V) = algebraMap F E r • w := hp
        have hpA : algebraMap F E r • w ∈ A := A.smul_mem _ hwA
        have h0 : (p : V) = 0 := by
          rw [← hsp p, hp', pB_apply]
          rw [Submodule.projectionOnto_apply_eq_zero_iff hAB.symm |>.2 hpA]
          rfl
        have hp0 : p = 0 := Subtype.ext h0
        have hrw0 : algebraMap F E r • w = 0 := by rw [← hp', hp0, map_zero]; rfl
        have : (algebraMap F E (r : F)⁻¹) • (algebraMap F E r • w) = w := by
          rw [smul_smul, ← map_mul, inv_mul_cancel₀ hr0, map_one, one_smul]
        rw [← this, hrw0, smul_zero]
      · rw [eq_top_iff, ← hL.2.1, Submodule.span_le]
        intro l hl
        have : l = d ⟨l, hl⟩ + (s (π ⟨l, hl⟩) : V) := by simp [d]
        rw [this]
        exact Submodule.add_mem_sup (hdA _) (hsW _)
    let pA' := A.projectionOnto W hcompl
    have hpA'd : ∀ l : abelian₂, (pA' l : V) = d l := by
      intro l
      have : (l : V) = d l + (s (π l) : V) := by simp [d]
      rw [this, map_add (f := _), Submodule.projectionOnto_apply_of_mem_right hcompl (hsW _), add_zero,
        Submodule.projectionOnto_apply_of_mem_left hcompl (hdA l)]
    let f : V →ₗ[E] E := hlin H u ∘ₗ A.subtype ∘ₗ pA'
    have hfA : ∀ y ∈ A, f y = H.h y u := by
      intro y hy
      show H.h (pA' y : V) u = H.h y u
      rw [Submodule.projectionOnto_apply_of_mem_left hcompl hy]
    have hfL : ∀ l : abelian₂, f l = H.h (d l) u := by
      intro l
      show H.h (pA' l : V) u = H.h (d l) u
      rw [hpA'd]
    obtain ⟨x, hx⟩ := hR M V H f
    have hxL : x ∈ abelian₂ := by
      refine (hL.2.2 x).2 (fun y hy => ?_)
      rw [H.h_herm y x, hx y, hfL ⟨y, hy⟩, H.h_herm u (d ⟨y, hy⟩)]
      exact PI.LocHerm.SlopeTestRemainingChoices.cj_mem_O M.L _
        (PI.LocHerm.SlopeTestRemainingChoices.cj_mem_O M.L _ (hyp _ (hdL _) (hdA _)))
    refine ⟨x, hxL, ?_⟩
    set z : V := (A.projectionOnto B hAB x : V) - u with hz
    have hzA : z ∈ A := A.sub_mem (A.projectionOnto B hAB x).2 hu
    have key : ∀ a ∈ A, H.h a z = 0 := by
      intro a ha
      have hxB := sub_proj_mem hAB x
      have e1 : H.h a x = H.h a (A.projectionOnto B hAB x : V) := by
        have e2 := h_add_right H a (A.projectionOnto B hAB x : V) (x - (A.projectionOnto B hAB x : V))
        rw [add_sub_cancel, (orth a ha _ hxB).1, add_zero] at e2
        exact e2
      rw [hz, h_sub_right, ← e1, hx a, hfA a ha, sub_self]
    have hz0 : z = 0 := by
      refine H.nondeg z (fun v => ?_)
      have hvB := sub_proj_mem hAB v
      have e3 := h_add_right H z (A.projectionOnto B hAB v : V) (v - (A.projectionOnto B hAB v : V))
      rw [add_sub_cancel, (orth z hzA _ hvB).1, add_zero] at e3
      rw [e3, H.h_herm _ z, key _ (A.projectionOnto B hAB v).2, map_zero]
    exact sub_eq_zero.1 hz0

end PI.LocHerm.Glue
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.RieszRepresentationHolds
section
noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

theorem rieszRepresentation_holds : Riesz := by
  intro F _ _ _ E _ _ _ _ M V _ _ H f
  have : Module.Free F E := M.L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have : Module.Free E V := H.free
  have : Module.Finite E V := H.fin
  let b := Module.Free.chooseBasis E V
  let ℓ : V → V →ₗ[E] E := fun y =>
    { toFun := fun v => H.h v y
      map_add' := fun v w => H.h_add_left v w y
      map_smul' := fun c v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact H.h_smul_left c v y }
  have hℓ : ∀ v y, ℓ y v = H.h v y := fun _ _ => rfl
  have key : ∀ (v : V) (a : Module.Free.ChooseBasisIndex E V → E),
      H.h v (∑ j, a j • b j) = ∑ j, M.L.cj (a j) * H.h v (b j) := by
    intro v a
    rw [H.h_herm (∑ j, a j • b j) v]
    have hs : H.h (∑ j, a j • b j) v = ∑ j, a j * H.h (b j) v := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hℓ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hℓ, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  let A : Matrix (Module.Free.ChooseBasisIndex E V) (Module.Free.ChooseBasisIndex E V) E :=
    Matrix.of fun i j => H.h (b i) (b j)
  have hA : ∀ u i, H.h (b i) (∑ j, M.L.cj (u j) • b j) = A.mulVecLin u i := by
    intro u i
    rw [key, Matrix.mulVecLin_apply]
    simp only [M.L.cj_cj, Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hext : ∀ (x : V) (g : V →ₗ[E] E), (∀ i, H.h (b i) x = g (b i)) → ∀ v, H.h v x = g v := by
    intro x g hg v
    have : ℓ x = g := b.ext fun i => by rw [hℓ]; exact hg i
    rw [← hℓ, this]
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hx : ∀ v, H.h v (∑ j, M.L.cj (u j) • b j) = (0 : V →ₗ[E] E) v := by
      refine hext _ 0 fun i => ?_
      rw [hA, hu]
      rfl
    have hx0 : (∑ j, M.L.cj (u j) • b j) = 0 := by
      refine H.nondeg _ fun y => ?_
      rw [H.h_herm y, hx y, LinearMap.zero_apply, map_zero]
    have hc : (fun j => M.L.cj (u j)) = 0 := by
      apply b.equivFun.symm.injective
      rw [Module.Basis.equivFun_symm_apply, hx0, map_zero]
    funext j
    have := congrFun hc j
    simp only [Pi.zero_apply] at this
    have h2 := congrArg M.L.cj this
    rw [M.L.cj_cj, map_zero] at h2
    exact h2
  obtain ⟨u, hu⟩ := IsArtinian.surjective_of_injective_endomorphism A.mulVecLin hinj
    (fun i => f (b i))
  refine ⟨∑ j, M.L.cj (u j) • b j, hext _ f fun i => ?_⟩
  rw [hA, hu]

end PI.LocHerm.Glue
end
end

