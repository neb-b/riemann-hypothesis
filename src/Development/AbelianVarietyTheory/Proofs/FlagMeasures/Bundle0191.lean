module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamental
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentralMapMemIntegralUnipotentFixingFrame
section
noncomputable section

namespace GlobalTheory.LoopC.Centre

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def nil (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) : S.V →ₗ[E] S.V :=
  ∑ a, ∑ a', (c a a' • S.hT (e a')).smulRight (e a)

theorem nil_apply (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V) :
    nil e c x = ∑ a, ∑ a', (c a a' * S.hT (e a') x) • e a := by
  simp [nil]

theorem nil_eq_zero (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V)
    (hx : ∀ a, S.hT (e a) x = 0) : nil e c x = 0 := by
  rw [nil_apply]
  simp [hx]

theorem hT_nil (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) (a : Fin r) : S.hT (e a) (nil e c x) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [nil_apply, map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun b' _ => ?_
  rw [LinearMap.map_smul, he, smul_zero]

def cen (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E) :
    S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (LinearMap.id + nil e c) (LinearMap.id - nil e c)
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])

theorem cen_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) : cen e he c x = x + nil e c x := rfl

theorem cen_symm_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0)
    (c : Matrix (Fin r) (Fin r) E) (x : S.V) : (cen e he c).symm x = x - nil e c x := rfl

theorem cen_isom (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (hc : cᴴ = -c) : cen e he c ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hstar : ∀ a a', starRingEnd E (c a a') = -c a' a := by
    intro a a'
    have h := congrFun (congrFun hc a') a
    rw [starRingEnd_apply]
    simpa [Matrix.conjTranspose_apply] using h
  have hsym : ∀ u v, starRingEnd E (S.hT u v) = S.hT v u := S.herm.eq

  have hnn : ∀ x y, S.hT (nil e c x) (nil e c y) = 0 := by
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [nil_apply e c x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_nil e he c y a, smul_zero]

  have hcross : ∀ x y, S.hT (nil e c x) y + S.hT x (nil e c y) = 0 := by
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [nil_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.map_smul, smul_eq_mul, map_mul, RingHom.id_apply, hstar, hsym]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a' _ => ?_
    ring
  show ∀ x y, S.hT (cen e he c x) (cen e he c y) = S.hT x y
  intro x y
  rw [cen_apply, cen_apply]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [hnn, add_zero]
  linear_combination hcross x y

theorem nil_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (e : Fin r → S.V)
    (heΛ : ∀ a, e a ∈ Λ) (c : Matrix (Fin r) (Fin r) (𝓞 E)) (x : S.V) (hx : x ∈ Λ) :
    nil e (c.map (algebraMap (𝓞 E) E)) x ∈ Λ := by
  rw [nil_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun a' _ => ?_
  have hd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    have h' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hΛ
    rw [h']
    exact hx
  have h1 : S.hT (e a') x ∈ (1 : Submodule (𝓞 E) E) := by
    have h2 := (Submodule.mem_iInf _).mp hd (e a')
    have h3 := (Submodule.mem_iInf _).mp h2 (heΛ a')
    exact h3
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
  rw [Matrix.map_apply, ← ho, ← map_mul, algebraMap_smul]
  exact Λ.smul_mem _ (heΛ a)

theorem centre_gen {T : E} (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (heΛ : ∀ a, F.fl.e a ∈ Λ)
    (c : Matrix (Fin r) (Fin r) (𝓞 E))
    (hc : (c.map (algebraMap (𝓞 E) E))ᴴ = -c.map (algebraMap (𝓞 E) E)) :
    ∃ n : S.V ≃ₗ[E] S.V, (n ∈ NLam Λ F ∧ ∀ b, n (frame F b) = frame F b) ∧
      (∀ x ∈ orth S (Xsp F), n x = x) ∧
      ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : E) * S.hT (F.fl.e a') x) • F.fl.e a := by
  have hiso : ∀ a b, S.hT (F.fl.e a) (F.fl.e b) = 0 := F.fl.e_iso

  have hXz : ∀ a', ∀ x ∈ Xsp F, S.hT (F.fl.e a') x = 0 := by
    intro a' x hx
    have hle : Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a')) := by
      show Submodule.span E (Set.range F.fl.e) ≤ _
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact LinearMap.mem_ker.mpr (hiso a' b)
    exact LinearMap.mem_ker.mp (hle hx)
  have hXe : ∀ a, F.fl.e a ∈ Xsp F := by
    intro a
    show F.fl.e a ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨a, rfl⟩

  have hfix : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x = x := by
    intro x hx
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    have h2 := (Submodule.mem_iInf _).mp hx (F.fl.e a')
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h2 (hXe a'))

  have hframe : ∀ b, cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) (frame F b) = frame F b := by
    intro b
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    induction b using Fin.lastCases with
    | last => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using F.fl.z_orth a'
    | cast i => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using hiso a' i

  have hflag : ∀ j, ∀ x ∈ Xflag F (j + 1),
      cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xflag F j := by
    intro j x hx
    have hle : Xflag F (j + 1) ≤ Xsp F := by
      show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ Submodule.span E (Set.range F.fl.e)
      exact Submodule.span_mono (Set.image_subset_range _ _)
    rw [cen_apply, nil_eq_zero _ _ _ (fun a' => hXz a' x (hle hx)), add_zero, sub_self]
    exact zero_mem _
  have horth : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xsp F := by
    intro x hx
    rw [hfix x hx, sub_self]
    exact zero_mem _

  have hmap : Formalism.HermitianLatticesTheory.gmap (cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E))) Λ = Λ := by
    show Submodule.map _ Λ = Λ
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x ∈ Λ
      rw [cen_apply]
      exact Λ.add_mem hx (nil_mem Λ hΛ _ heΛ c x hx)
    · intro y hy
      refine Submodule.mem_map.mpr ⟨y - nil F.fl.e (c.map (algebraMap (𝓞 E) E)) y,
        Λ.sub_mem hy (nil_mem Λ hΛ _ heΛ c y hy), ?_⟩
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) _ = y
      rw [← cen_symm_apply F.fl.e hiso _ y]
      exact LinearEquiv.apply_symm_apply _ y
  have hN : cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) ∈ NLam Λ F := by
    simp only [NLam, IsAutLam, Set.mem_setOf_eq]
    exact ⟨⟨cen_isom _ _ _ hc, hmap⟩, hflag, horth⟩
  refine ⟨cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)), ⟨hN, hframe⟩, hfix, fun x => ?_⟩
  rw [cen_apply, nil_apply]
  rfl

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem centralMap_mem_integralUnipotentFixingFrame : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (Λ : LatV D), Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → (∀ a, F.fl.e a ∈ Λ) → ∀ c : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E), (c.map (algebraMap (𝓞 D.host.E) D.host.E))ᴴ = -c.map (algebraMap (𝓞 D.host.E) D.host.E) → ∃ n ∈ N1 D Λ F, (∀ x ∈ orth (hS D) (Xsp F), n x = x) ∧ ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : D.host.E) * (hS D).hT (F.fl.e a') x) • F.fl.e a := by
  intro D T F Λ hΛ heΛ c hc
  obtain ⟨n, h1, hfix, hform⟩ := centre_gen F Λ hΛ heΛ c hc
  exact ⟨n, h1, hfix, hform⟩

end GlobalTheory.LoopC.Centre

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagFlagAdaptedLatticeBasis
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem eq_top_of_map_lattice_mem {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {m : ℕ}
    (Λ : Submodule (𝓞 E) (Fin m → E)) (hΛ : Submodule.span E (Λ : Set (Fin m → E)) = ⊤)
    (W : Submodule ℂ (Fin m → ℂ)) (h : ∀ t ∈ Λ, (fun l => φ (t l)) ∈ W) : W = ⊤ := by

  have hall : ∀ x : Fin m → E, (fun l => φ (x l)) ∈ W := by
    intro x
    have hx : x ∈ Submodule.span E (Λ : Set (Fin m → E)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem t ht => exact h t ht
    | zero =>
      have e1 : (fun l => φ ((0 : Fin m → E) l)) = 0 := by
        funext l; simp
      rw [e1]; exact W.zero_mem
    | add x y _ _ hx hy =>
      have e1 : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + (fun l => φ (y l)) := by
        funext l; simp
      rw [e1]; exact W.add_mem hx hy
    | smul c x _ hx =>
      have e1 : (fun l => φ ((c • x) l)) = φ c • (fun l => φ (x l)) := by
        funext l; simp
      rw [e1]; exact W.smul_mem _ hx

  have key : ∀ l, (Pi.single l (1 : ℂ) : Fin m → ℂ) ∈ W := by
    intro l
    convert hall (Pi.single l 1) using 1
    funext l'
    by_cases hl : l' = l
    · subst hl; simp
    · simp [hl]
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ l, w l • (Pi.single l (1 : ℂ) : Fin m → ℂ) := by
    funext l'; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact W.sum_mem fun l _ => W.smul_mem _ (key l)

theorem spansFlag_flagAt : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ v, SpansFlag (fun i => (I.P v)⁻¹ * (T i).map (I.φ v)) (flagAt I S v) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hA v k y
  obtain ⟨-, -, -, hiso, hpair, -, hlam, hS⟩ := hA

  have hspan (i : Fin a) : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) = ⊤ := by
    -- The dual frame projects the ambient lattice onto the i-th coordinate block.
    let p := ((T' i)ᴴ * I.J).mulVecLin
    have hJ : I.Jᴴ = I.J := by
      ext r s
      simpa [Formalism.UG.cT, starRingEnd_apply] using congrFun (congrFun I.J_herm r) s
    have hswap (b : Fin a) : (T' i)ᴴ * I.J * T b = ((T b)ᴴ * I.J * T' i)ᴴ := by
      simp [hJ, Matrix.mul_assoc]
    have hpT (x : Fin (j i) → I.E) : p (T i *ᵥ x) = x := by
      simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [hswap, (hpair i).1, Matrix.conjTranspose_one, Matrix.one_mulVec]
    have hple : Submodule.span I.E (lamX I (1, xf) : Set (Fin I.n → I.E)) ≤
        (Submodule.span I.E (Λ i : Set (Fin (j i) → I.E))).comap p := by
      refine Submodule.span_le.2 fun z hz => ?_
      obtain ⟨u, u', z₀, hu, -, -, rfl⟩ := (hlam z).1 hz
      have hsum : p (∑ b, T b *ᵥ u b) = u i := by
        rw [map_sum, Finset.sum_eq_single i, hpT]
        · intro b _ hbi
          simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
          rw [hswap, (hiso b i).2.2 hbi, Matrix.conjTranspose_zero, Matrix.zero_mulVec]
        · simp
      have hsum' : p (∑ b, T' b *ᵥ u' b) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun b _ => ?_
        simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rw [(hiso i b).2.1, Matrix.zero_mulVec]
      have hp₀ (x : Fin I₀.n → I.E) : p (T₀ *ᵥ x) = 0 := by
        simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rw [(hpair i).2.2, Matrix.zero_mulVec]
      change p _ ∈ Submodule.span I.E (Λ i : Set (Fin (j i) → I.E))
      rw [map_add, map_add, hsum, hsum', hp₀, add_zero, add_zero]
      exact Submodule.subset_span (hu i)
    rw [(GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.2.1] at hple
    refine eq_top_iff.2 fun x _ => ?_
    have hx := hple (Submodule.mem_top (x := T i *ᵥ x))
    rwa [Submodule.mem_comap, hpT] at hx

  have himg : ∀ u : ∀ i, Fin (j i) → I.E,
      ((I.P v)⁻¹ *ᵥ fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, ((I.P v)⁻¹ * (T i).map (I.φ v)) *ᵥ (fun l => I.φ v (u i l)) := by
    intro u
    have e1 : (fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, (T i).map (I.φ v) *ᵥ (fun l => I.φ v (u i l)) := by
      funext l
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, map_sum, RingHom.map_mulVec, Function.comp_def]
    rw [e1, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.mulVec_mulVec _ _ _
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨u, -, hk, rfl⟩ := (hS k z).1 hz
      refine ⟨fun i l => I.φ v (u i l), fun i hi => ?_, himg u⟩
      funext l
      simp [hk i hi]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', rfl⟩ := hy
      refine ⟨u + u', fun i hi => by simp [hu i hi, hu' i hi], ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_add _ _ _).symm
    | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨c • u, fun i hi => by simp [hu i hi], ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_smul _ _ _).symm
  · rintro ⟨u, hu, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hik : i.castSucc < k
    · have htop := eq_top_of_map_lattice_mem (I.φ v) (Λ i) (hspan i)
        ((flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v)))) (by
          intro t ht
          rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
          let w : ∀ i', Fin (j i') → I.E := Pi.single i t
          have hw1 : ∀ i', w i' ∈ Λ i' := by
            intro i'
            by_cases h' : i' = i
            · subst h'; simpa [w] using ht
            · simp [w, Pi.single_eq_of_ne h']
          have hw2 : ∀ i' : Fin a, ¬ i'.castSucc < k → w i' = 0 := by
            intro i' hi'
            have h' : i' ≠ i := by rintro rfl; exact hi' hik
            simp [w, Pi.single_eq_of_ne h']
          have hz : (∑ i', T i' *ᵥ w i') ∈ S k := (hS k _).2 ⟨w, hw1, hw2, rfl⟩
          have hmem := Submodule.subset_span (R := ℂ) (Set.mem_image_of_mem
            (fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) hz)
          have hsum := himg w
          rw [hsum, Finset.sum_eq_single i] at hmem
          · simp [w] at hmem
            exact hmem
          · intro i' _ h'
            simp [w, Pi.single_eq_of_ne h']
            exact Matrix.mulVec_zero _
          · simp)
      have : u i ∈ (flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v))) := by
        rw [htop]; trivial
      simpa [Submodule.mem_comap, Matrix.mulVecLin_apply] using this
    · simp [hu i hik]

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexFlagAtEmbeddingFrameFinrankAndLowers
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

private lemma linearIndependent_map_ringHom_complex {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) {ι : Type}
    [Fintype ι] {v : ι → Fin n → E} (hv : LinearIndependent E v) :
    LinearIndependent ℂ (fun i l => φ (v i l)) := by
  classical

  let f : (ι → E) →ₗ[E] (Fin n → E) := Fintype.linearCombination E v
  have hf : ∀ c, f c = ∑ i, c i • v i := fun c => Fintype.linearCombination_apply E v c
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [hf] at hc
    funext i
    exact (Fintype.linearIndependent_iff.mp hv) c hc i
  obtain ⟨L, hL⟩ := f.exists_leftInverse_of_injective hker
  have hB : ∀ i, LinearMap.toMatrix' L *ᵥ v i = Pi.single i 1 := by
    intro i
    rw [LinearMap.toMatrix'_mulVec]
    have h1 := LinearMap.congr_fun hL (Pi.single i 1)
    have h2 : f (Pi.single i 1) = v i := by
      rw [hf]
      simp [Pi.single_apply]
    rw [LinearMap.comp_apply, h2] at h1
    exact h1
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hcol : ∀ i k, ((LinearMap.toMatrix' L).map φ *ᵥ fun l => φ (v i l)) k
      = if k = i then 1 else 0 := by
    intro i k
    have h3 := RingHom.map_mulVec φ (LinearMap.toMatrix' L) (v i) k
    rw [hB i] at h3
    rw [show (fun l => φ (v i l)) = φ ∘ v i from rfl, ← h3]
    by_cases hki : k = i
    · subst hki; simp
    · simp [hki]
  have h4 := congrArg (fun w => ((LinearMap.toMatrix' L).map φ *ᵥ w) j) hc
  simp only [Matrix.mulVec_zero, Pi.zero_apply] at h4
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h4, ← Matrix.mulVecLin_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, Matrix.mulVecLin_apply, hcol, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma map_mem_span_image_of_mem_span {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (t : Set (Fin n → E)) {x : Fin n → E} (hx : x ∈ Submodule.span E t) :
    (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' t) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have h0 : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    rw [h0]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have h1 : (fun l => φ ((y + z) l)) = (fun l => φ (y l)) + (fun l => φ (z l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have h1 : (fun l => φ ((c • y) l)) = φ c • (fun l => φ (y l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.smul_mem _ _ hy

theorem finrank_span_image_ringHom {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (s : Set (Fin n → E)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s))
      = Module.finrank E (Submodule.span E s) := by
  classical
  let V := Submodule.span E s
  let b := Module.finBasis E V
  let v : Fin (Module.finrank E V) → Fin n → E := fun i => (b i : Fin n → E)
  have hv : LinearIndependent E v := b.linearIndependent.map' V.subtype V.ker_subtype
  have hvV : ∀ i, v i ∈ V := fun i => (b i).2
  have hspan : Submodule.span E (Set.range v) = V := by
    have hr : Set.range v = V.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have heq : Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s)
      = Submodule.span ℂ (Set.range fun i l => φ (v i l)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span E (Set.range v) := by
        rw [hspan]; exact Submodule.subset_span hx
      have h := map_mem_span_image_of_mem_span φ _ hx'
      rw [← Set.range_comp] at h
      exact h
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact map_mem_span_image_of_mem_span φ s (hvV i)
  rw [heq, finrank_span_eq_card (linearIndependent_map_ringHom_complex φ hv), Fintype.card_fin]

theorem finrank_locFlag_and_lowers (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : E →+* ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (hP : IsUnit P) :
    (∀ b, Module.finrank ℂ (locFlag φ P F b) = Formalism.HN.rkK (F b)) ∧
      ∀ c, ∀ T ∈ lowers F c, P⁻¹ * T.map φ * P ∈ lowers (locFlag φ P F) c := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  refine ⟨fun b => ?_, fun c T hT => ?_⟩
  · have hinj : Function.Injective (Matrix.mulVecLin P⁻¹) := by
      intro x y hxy
      have h := congrArg (fun z => P *ᵥ z) hxy
      simpa [Matrix.mulVec_mulVec, hPP] using h
    have himg : locFlag φ P F b = Submodule.map (Matrix.mulVecLin P⁻¹)
        (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' (F b : Set (Fin n → E)))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      rfl
    rw [himg, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_span_image_ringHom]
    rfl
  · rw [GlobalTheory.RadCov.mem_lowers] at hT ⊢
    intro b y hy
    have key : locFlag φ P F (b + c + 1)
        ≤ Submodule.comap (Matrix.mulVecLin (P⁻¹ * T.map φ * P)) (locFlag φ P F b) := by
      rw [locFlag, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      refine Submodule.subset_span ⟨T *ᵥ x, hT b x hx, ?_⟩
      have h1 : (fun l => φ ((T *ᵥ x) l)) = T.map φ *ᵥ (fun l => φ (x l)) := by
        funext l; exact RingHom.map_mulVec φ T x l
      dsimp only
      rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P⁻¹ * T.map φ) P P⁻¹,
        hPP, Matrix.mul_one]
    exact key hy

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamentalStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < detNorm E j g} ∧ (∀ g, 0 < detNorm E j g → ∃ γ ∈ autGL E j Λ, γ * g ∈ D) ∧ (∀ g ∈ D, ∀ t : ℝ, 0 < t → (fun w a b => (t : ℂ) * g w a b) ∈ D) ∧ ∀ (G : MatInf E j → ENNReal) (A : Set (MatInf E j)), Measurable (fun g => {g | 0 < detNorm E j g}.indicator G g) → (∀ γ ∈ autGL E j Λ, ∀ g, 0 < detNorm E j g → G (γ * g) = G g) → MeasurableSet A → A ⊆ {g | 0 < detNorm E j g} → (∀ γ ∈ autGL E j Λ, ∀ g ∈ A, γ * g ∈ A) → covol (autGL E j Λ) (((haarGL E j).restrict {g | 0 < detNorm E j g}).withDensity G) A = ∫⁻ g in A ∩ D, G g ∂(haarGL E j) := by
  first
  | exact @GlobalTheory.LatDom.exists_cone_domain
  | intro E _ _ hE j Λ hΛ
    exact GlobalTheory.LatDom.exists_cone_domain E hE j Λ hΛ.toIsLattice
end

