module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgebraActionBundleFiltrationStep
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

section Basic

variable {K A V : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V]

theorem apply_mem_idealV (τ : A →+* Module.End K V) {J : Ideal A} {a : A} (ha : a ∈ J) (v : V) :
    τ a v ∈ idealV τ J :=
  Submodule.mem_iSup_of_mem (⟨a, ha⟩ : J) (LinearMap.mem_range_self _ v)

theorem idealV_le (τ : A →+* Module.End K V) {J : Ideal A} {W : Submodule K V}
    (h : ∀ a ∈ J, ∀ v, τ a v ∈ W) : idealV τ J ≤ W :=
  iSup_le fun a => by
    rintro _ ⟨v, rfl⟩
    exact h a a.2 v

theorem apply_mem_of_mul_mem (τ : A →+* Module.End K V) {U J₁ : Ideal A} {t : A}
    (h : ∀ a ∈ U, a * t ∈ J₁) {μ : V} (hμ : μ ∈ idealV τ U) : τ t μ ∈ idealV τ J₁ := by
  have : idealV τ U ≤ (idealV τ J₁).comap (τ t) := idealV_le τ fun a ha v => by
    rw [Submodule.mem_comap]
    show τ t (τ a v) ∈ _
    rw [← Module.End.mul_apply, ← map_mul, mul_comm]
    exact apply_mem_idealV τ (h a ha) v
  exact this hμ

end Basic

section Coord

variable {K A V k : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V] [Field k]
  [Algebra k K] [Algebra k A]

theorem coord_vanish (τ : A →+* Module.End K V) {r : ℕ} (x : Fin r → V) (Θ : Fin r → V →ₗ[K] K)
    (l : A →ₗ[k] k)
    (hΘ : ∀ s s' a, Θ s (τ a (x s')) = if s = s' then algebraMap k K (l a) else 0)
    (hspan : ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)))
    {U : Ideal A} (hl : ∀ a ∈ U, l a = 0) (s : Fin r) {y : V} (hy : y ∈ idealV τ U) :
    Θ s y = 0 := by
  have : idealV τ U ≤ LinearMap.ker (Θ s) := idealV_le τ fun u hu v => by
    have h : Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)) ≤
        (LinearMap.ker (Θ s)).comap (τ u) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨a, s'⟩, rfl⟩
      show Θ s (τ u (τ a (x s'))) = 0
      rw [← Module.End.mul_apply, ← map_mul, hΘ, hl _ (U.mul_mem_right a hu)]
      simp
    exact h (hspan v)
  exact this hy

theorem exists_coords (τ : A →+* Module.End K V) {r : ℕ} (x : Fin r → V) (χ : A →ₐ[k] k)
    (hc : ∀ (c : k) (y : V), τ (algebraMap k A c) y = algebraMap k K c • y)
    (hspan : ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)))
    (v : V) : ∃ d : Fin r → K, v - ∑ s, d s • x s ∈ idealV τ (RingHom.ker χ) := by
  have h : Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2)) ≤
      Submodule.span K (Set.range x) ⊔ idealV τ (RingHom.ker χ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, s⟩, rfl⟩
    have ha : a - algebraMap k A (χ a) ∈ RingHom.ker χ := by
      simp [RingHom.mem_ker]
    have e : τ a (x s) = algebraMap k K (χ a) • x s + τ (a - algebraMap k A (χ a)) (x s) := by
      rw [map_sub, LinearMap.sub_apply, hc]
      abel
    show τ a (x s) ∈ _
    rw [e]
    exact Submodule.add_mem_sup
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)) (apply_mem_idealV τ ha _)
  obtain ⟨p, hp, μ, hμ, e⟩ := Submodule.mem_sup.1 (h (hspan v))
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hp
  refine ⟨d, ?_⟩
  rw [hd, ← e, add_sub_cancel_left]
  exact hμ

theorem exists_of_mem_idealV (τ : A →+* Module.End K V) {J₁ J : Ideal A} {t : A}
    (hc : ∀ (c : k) (y : V), τ (algebraMap k A c) y = algebraMap k K c • y)
    (hJt : ∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) {y : V} (hy : y ∈ idealV τ J) :
    ∃ z, y - τ t z ∈ idealV τ J₁ := by
  have h : idealV τ J ≤ LinearMap.range (τ t) ⊔ idealV τ J₁ := idealV_le τ fun a ha v => by
    obtain ⟨c, hc'⟩ := hJt a ha
    have e : τ a v = τ t (algebraMap k K c • v) + τ (a - algebraMap k A c * t) v := by
      rw [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply, hc, map_smul]
      abel
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (apply_mem_idealV τ hc' v)
  obtain ⟨p, ⟨z, rfl⟩, w, hw, e⟩ := Submodule.mem_sup.1 (h hy)
  refine ⟨z, ?_⟩
  rw [← e, add_sub_cancel_left]
  exact hw

end Coord

section Local

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
  {L : C.I → AddSubgroup V} {k A : Type} [Field k] [Algebra k K] [CommRing A] [Algebra k A]

theorem exists_local (τ : A →+* Module.End K V) {r : ℕ} (χ : A →ₐ[k] k) {J₁ J : Ideal A} {t : A}
    (l : A →ₗ[k] k) (hL : IsBun C L)
    (hc : ∀ (c : k) (y : V), τ (algebraMap k A c) y = algebraMap k K c • y) {i : C.I}
    (hF : FreeAt C k τ L r i)
    (hJt : ∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁)
    (hmt : ∀ a ∈ RingHom.ker χ, a * t ∈ J₁) (hl : ∀ a ∈ J₁, l a = 0) (hlt : l t = 1) :
    ∃ P : V →ₗ[K] V, (∀ y ∈ idealV τ J, y - τ t (P y) ∈ idealV τ J₁) ∧
      (∀ w ∈ idealV τ J₁, P w = 0) ∧
      (∀ z, P (τ t z) - z ∈ idealV τ (RingHom.ker χ)) ∧
      ∀ y ∈ L i, P y ∈ L i := by
  obtain ⟨x, Θ', hx, hΘ', hint, hspan⟩ := hF
  have hΘ := hΘ' l
  set Θ := Θ' l with hΘdef
  have hW1 : ∀ s, ∀ w ∈ idealV τ J₁, Θ s w = 0 := fun s w hw =>
    coord_vanish τ x Θ l hΘ hspan hl s hw
  let P : V →ₗ[K] V := ∑ s, (Θ s).smulRight (x s)
  have hPa : ∀ y, P y = ∑ s, Θ s y • x s := fun y => by
    simp [P, LinearMap.sum_apply]
  have hΘT : ∀ s s', Θ s (τ t (x s')) = if s = s' then 1 else 0 := fun s s' => by
    rw [hΘ, hlt, map_one]
  have hP0 : ∀ w ∈ idealV τ J₁, P w = 0 := fun w hw => by
    rw [hPa]
    exact Finset.sum_eq_zero fun s _ => by rw [hW1 s w hw, zero_smul]

  have hPc : ∀ (d : Fin r → K) (y : V), y - ∑ s, d s • τ t (x s) ∈ idealV τ J₁ →
      P y = ∑ s, d s • x s := fun d y hy => by
    have h1 : ∀ s, Θ s y = d s := fun s => by
      have h2 := hW1 s _ hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_eq_zero] at h2
      rw [h2]
      simp [hΘT]
    rw [hPa]
    exact Finset.sum_congr rfl fun s _ => by rw [h1 s]
  have hT : ∀ z, ∃ d : Fin r → K, z - ∑ s, d s • x s ∈ idealV τ (RingHom.ker χ) ∧
      τ t z - ∑ s, d s • τ t (x s) ∈ idealV τ J₁ := fun z => by
    obtain ⟨d, hd⟩ := exists_coords τ x χ hc hspan z
    refine ⟨d, hd, ?_⟩
    have := apply_mem_of_mul_mem τ hmt hd
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sub, map_sum] using this
  have hPT : ∀ z, P (τ t z) - z ∈ idealV τ (RingHom.ker χ) := fun z => by
    obtain ⟨d, h1, h2⟩ := hT z
    rw [hPc d _ h2, ← neg_sub]
    exact neg_mem h1
  refine ⟨P, fun y hy => ?_, hP0, hPT, fun y hy => ?_⟩
  · obtain ⟨z, hz⟩ := exists_of_mem_idealV τ hc hJt hy
    obtain ⟨d, -, h2⟩ := hT z
    have h3 : y - ∑ s, d s • τ t (x s) ∈ idealV τ J₁ := by
      have := add_mem hz h2
      simpa using this
    rw [hPc d _ h3]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum] using h3
  · rw [hPa]
    exact sum_mem fun s _ => smul_mem_of_isBun C hL i (hint l s y hy) (hx s)

end Local

theorem subDeg_step : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (k A : Type) [Field k] [Algebra k K] [CommRing A] [Algebra k A] (τ : A →+* Module.End K V) (r : ℕ) (χ : A →ₐ[k] k) (J₁ J : Ideal A) (t : A) (l : A →ₗ[k] k), IsBun C L → (∀ a, IsHom C L L (τ a)) → (∀ (c : k) (x : V), τ (algebraMap k A c) x = algebraMap k K c • x) → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → (∀ i, FreeAt C k τ L r i) → J₁ ≤ J → t ∈ J → (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) → (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) → (∀ a ∈ J₁, l a = 0) → l t = 1 → subDeg C L (idealV τ J) = subDeg C L (idealV τ J₁) + deg C (quot C L (idealV τ (RingHom.ker χ))) := by
  intro K _ C V _ _ _ L k A _ _ _ _ τ r χ J₁ J t l hL hτ hc _ hF hJ ht hJt hmt hl hlt
  rcases isEmpty_or_nonempty C.I with hI | ⟨⟨i₀⟩⟩
  · simp [subDeg, deg, finsum_of_isEmpty]
  have hW : idealV τ J₁ ≤ idealV τ J :=
    idealV_le τ fun a ha v => apply_mem_idealV τ (hJ ha) v
  choose P hP1 hP2 hP3 hP4 using fun i =>
    exists_local C τ χ l hL hc (hF i) hJt hmt hl hlt
  let g : idealV τ J →ₗ[K] V ⧸ idealV τ (RingHom.ker χ) :=
    (idealV τ (RingHom.ker χ)).mkQ ∘ₗ P i₀ ∘ₗ (idealV τ J).subtype
  have hg : ∀ y : idealV τ J, g y = Submodule.Quotient.mk (P i₀ y) := fun y => rfl
  have hgT : ∀ z, g ⟨τ t z, apply_mem_idealV τ ht z⟩ = Submodule.Quotient.mk z := fun z => by
    rw [hg]
    exact (Submodule.Quotient.eq _).2 (hP3 i₀ z)
  have hS : ShortExact C (sub C L (idealV τ J₁)) (sub C L (idealV τ J))
      (quot C L (idealV τ (RingHom.ker χ))) (Submodule.inclusion hW) g := by
    refine ⟨Submodule.inclusion_injective hW, fun y => ⟨fun h => ?_, ?_⟩, fun z => ?_,
      fun i x => Iff.rfl, fun i z => ⟨?_, ?_⟩⟩
    · rw [hg, Submodule.Quotient.mk_eq_zero] at h
      have h2 := hP1 i₀ y y.2
      have h3 := apply_mem_of_mul_mem τ hmt h
      have h4 : (y : V) ∈ idealV τ J₁ := by simpa using add_mem h2 h3
      exact ⟨⟨y, h4⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      rw [hg]
      show Submodule.Quotient.mk (P i₀ (w : V)) = 0
      rw [hP2 i₀ w w.2]
      simp
    · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact ⟨_, hgT z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨τ t z, apply_mem_idealV τ ht z⟩, hτ t i z hz, hgT z⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨P i y, hP4 i y hy, ?_⟩
      have h1 : P i₀ (y : V) = P i₀ (τ t (P i y)) := by
        have := hP2 i₀ _ (hP1 i y y.2)
        rwa [map_sub, sub_eq_zero] at this
      rw [hg, h1]
      exact ((Submodule.Quotient.eq _).2 (hP3 i₀ (P i y))).symm
  have hB := (SubQuot.isBun_sub_quot K C V L (idealV τ J) hL).1
  exact (deg_shortExact K C _ _ _ _ _ _ _ _ hB hS).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationQuotientEquivLatticeStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_quotient_equiv_lattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords | exact GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeFibreIdealLocallyFree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_annSub_iff {n k : ℕ} {v : Fin n → Ω} :
    v ∈ annSub Ω n k ↔ ∀ j : Fin n, (j : ℕ) < k → v j = 0 := by
  simp [annSub, Submodule.mem_pi]

def stepCoord (Ω : Type) [Field Ω] {n : ℕ} (i : Fin n) : annSub Ω n i →ₗ[Ω] Ω :=
  (LinearMap.proj i).comp (annSub Ω n i).subtype

theorem stepCoord_apply {n : ℕ} (i : Fin n) (v : annSub Ω n i) :
    stepCoord Ω i v = (v : Fin n → Ω) i := rfl

theorem stepCoord_surjective {n : ℕ} (i : Fin n) : Function.Surjective (stepCoord Ω i) := by
  classical
  intro c
  refine ⟨⟨Pi.single i c, mem_annSub_iff.2 fun j hj => ?_⟩, by simp [stepCoord_apply]⟩
  have : j ≠ i := by rintro rfl; exact lt_irrefl _ hj
  simp [Pi.single_apply, this]

theorem mem_ker_stepCoord {n : ℕ} (i : Fin n) (v : annSub Ω n i) :
    v ∈ LinearMap.ker (stepCoord Ω i) ↔ (v : Fin n → Ω) ∈ annSub Ω n ((i : ℕ) + 1) := by
  rw [LinearMap.mem_ker, stepCoord_apply, mem_annSub_iff]
  constructor
  · intro h j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact mem_annSub_iff.1 v.2 j hj
    · rw [Fin.ext hj]; exact h
  · intro h
    exact h i (Nat.lt_succ_self _)

theorem summand_step {n : ℕ} {L : AddSubgroup (Fin n → Ω)} (i : Fin n)
    (h : Summand L (annSub Ω n ((i : ℕ) + 1))) :
    Summand (L.comap (annSub Ω n i).subtype.toAddMonoidHom) (LinearMap.ker (stepCoord Ω i)) := by
  obtain ⟨ρ, h1, h2, h3⟩ := h
  have hle : ∀ v, ρ v ∈ annSub Ω n i := fun v =>
    mem_annSub_iff.2 fun j hj => mem_annSub_iff.1 (h1 v) j (Nat.lt_succ_of_lt hj)
  refine ⟨(ρ.comp (annSub Ω n i).subtype).codRestrict _ fun v => hle _, fun v => ?_, fun u hu => ?_,
    fun v hv => ?_⟩
  · rw [mem_ker_stepCoord]
    exact h1 _
  · apply Subtype.ext
    exact h2 _ ((mem_ker_stepCoord i u).1 hu)
  · exact h3 _ hv

theorem locFree_step (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} (hL : LocFree R n L)
    (i : Fin n) (h₀ : Summand L (annSub Ω n i)) (h₁ : Summand L (annSub Ω n ((i : ℕ) + 1))) :
    LocFree R 1 ((L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i)) := by
  have hA := ((_root_.GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot R (annSub Ω n i) n 0 L hL).2 h₀).1
  have hB := ((_root_.GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot R (LinearMap.ker (stepCoord Ω i)) _ 0 _ hA).2 (summand_step i h₁)).2
  have hr : Module.finrank Ω (annSub Ω n i) - Module.finrank Ω (LinearMap.ker (stepCoord Ω i)) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (stepCoord Ω i)
    rw [LinearMap.range_eq_top.2 (stepCoord_surjective i), finrank_top, Module.finrank_self] at h
    omega
  rw [hr] at hB
  have hC := (locFree_map_mkQ_iff R (stepCoord Ω i) (stepCoord_surjective i) _).1 hB
  convert hC using 1
  ext c
  constructor
  · rintro ⟨v, ⟨hv, hv'⟩, rfl⟩
    exact ⟨⟨v, hv'⟩, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, ⟨hv, v.2⟩, rfl⟩

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 (D.dId R p (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB h1 h2
  obtain ⟨hg, hbc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main D R p w χ hc hB h1
  refine ⟨fun τ i => locFree_step R (hg τ).1 i (h2.ann τ i) (h2.ann τ ((i : ℕ) + 1)), ?_⟩
  intro C _ _ _ _ RC hRC τ i
  have haf := ((hbc C RC hRC).2 τ).1
  have hs := (_root_.GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange R RC hRC (bcMap Ω C (Fin n)) (isBaseChange_bcMap Ω C _)
    (D.af R p (χ τ)) (annSub Ω n i) (hg τ).1.1 (h2.ann τ i)).2
  rw [span_bcMap_annSub] at hs
  unfold LieLatticeData.dId
  rw [haf, hs]
  have hm := SpanExact.map_spanOver RC
    (bcMap Ω C (Fin n) '' ((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _) : Set (Fin n → Ω)))
    (LinearMap.proj i : (Fin n → C) →ₗ[C] C)
  have himg : algebraMap Ω C '' (((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _).map
      (Pi.evalAddMonoidHom (fun _ => Ω) i) : AddSubgroup Ω) : Set Ω) =
      (LinearMap.proj i : (Fin n → C) →ₗ[C] C) '' (bcMap Ω C (Fin n) ''
        ((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _) : Set (Fin n → Ω))) := by
    ext c
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  rw [himg, ← hm]
  rfl

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeGraphComapLocallyFree
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ}
  {Sg : Type} {r s : Sg → ℕ}

theorem mem_stepGraph_iff (D : LieLatticeData Ω F n Sg r s) (τ : Sg) (χ : F → Ω) (i : Fin n) (c : Ω)
    (m : Fin (r τ) → Ω) :
    (c, m) ∈ D.stepGraph τ χ i ↔
      ∃ g u, (g, m) ∈ D.Th τ ∧ u ∈ vanSub Ω F n ((i : ℕ) + 1) ∧
        c • (fun x : Fin n → F => χ (x i)) = g + u := by
  unfold LieLatticeData.stepGraph
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨⟨g, m'⟩, hy, ⟨u, m''⟩, hz, he⟩
    obtain ⟨hu, hm⟩ := AddSubgroup.mem_prod.1 hz
    have hm0 : m'' = 0 := hm
    subst hm0
    have h1 : g + u = c • (fun x : Fin n → F => χ (x i)) := congrArg Prod.fst he
    have h2 : m' + 0 = m := congrArg Prod.snd he
    rw [add_zero] at h2
    subst h2
    exact ⟨g, u, hy, hu, h1.symm⟩
  · rintro ⟨g, u, hg, hu, he⟩
    refine ⟨(g, m), hg, (u, 0), AddSubgroup.mem_prod.2 ⟨hu, rfl⟩, ?_⟩
    exact Prod.ext he.symm (add_zero m)

theorem vanSub_apply_zero {i : ℕ} {u : (Fin n → F) → Ω} (hu : u ∈ vanSub Ω F n i) : u 0 = 0 := by
  have h := (Submodule.mem_pi.1 hu) (0 : Fin n → F) (fun _ _ => rfl)
  simpa using h

theorem stepGraph_stable [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω} {p : ℕ} {w : Ω}
    (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (i : Fin n) :
    ∀ a ∈ R, ∀ v ∈ D.stepGraph τ χ i, a • v ∈ D.stepGraph τ χ i := by
  rintro a ha ⟨c, m⟩ h
  obtain ⟨g, u, hg, hu, he⟩ := (mem_stepGraph_iff D τ χ i c m).1 h
  refine (mem_stepGraph_iff D τ χ i (a • c) (a • m)).2
    ⟨a • g, a • u, (hB.stable τ a ha).2.2 (g, m) hg, Submodule.smul_mem _ _ hu, ?_⟩
  rw [smul_assoc, he, smul_add]

theorem fst_mem_xId_of_mem_stepGraph [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω}
    {p : ℕ} {w : Ω} (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (i : Fin n) {c : Ω}
    {m : Fin (r τ) → Ω} (h : (c, m) ∈ D.stepGraph τ χ i) : c ∈ D.xId χ i := by
  obtain ⟨g, u, hg, hu, he⟩ := (mem_stepGraph_iff D τ χ i c m).1 h
  have hgM : g ∈ D.M := (((hB.th τ).1 g).1 ⟨m, hg⟩).1
  refine AddSubgroup.mem_comap.2 (AddSubgroup.mem_sup.2 ⟨g, hgM, u, hu, ?_⟩)
  exact he.symm

theorem exists_mem_stepGraph_of_mem_xId [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω}
    {p : ℕ} {w : Ω} (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (h0 : χ 0 = 0) (i : Fin n) {c : Ω}
    (h : c ∈ D.xId χ i) : ∃ m, (c, m) ∈ D.stepGraph τ χ i := by
  obtain ⟨g, hg, u, hu, he⟩ := AddSubgroup.mem_sup.1 (AddSubgroup.mem_comap.1 h)
  have he' : g + u = c • (fun x : Fin n → F => χ (x i)) := he
  have hu0 : u 0 = 0 := vanSub_apply_zero hu
  have hg0 : g 0 = 0 := by
    have := congrFun he' 0
    simpa [h0, hu0] using this
  obtain ⟨m, hm⟩ := ((hB.th τ).1 g).2 ⟨hg, hg0⟩
  exact ⟨m, (mem_stepGraph_iff D τ χ i c m).2 ⟨g, u, hm, hu, he'.symm⟩⟩

theorem zero_mem_stepGraph_iff (D : LieLatticeData Ω F n Sg r s) (τ : Sg) (χ : F → Ω) (i : Fin n)
    (m : Fin (r τ) → Ω) : (0, m) ∈ D.stepGraph τ χ i ↔ m ∈ D.kk τ ((i : ℕ) + 1) := by
  rw [mem_stepGraph_iff]
  constructor
  · rintro ⟨g, u, hg, hu, he⟩
    rw [zero_smul] at he
    have hgu : g = -u := eq_neg_of_add_eq_zero_left he.symm
    refine ⟨(g, m), ⟨hg, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩, rfl⟩
    rw [hgu]
    exact neg_mem hu
  · rintro ⟨⟨g, m'⟩, ⟨hg, hp⟩, rfl⟩
    have hv : g ∈ vanSub Ω F n ((i : ℕ) + 1) := (AddSubgroup.mem_prod.1 hp).1
    refine ⟨g, -g, hg, neg_mem hv, ?_⟩
    simp

theorem stepKer : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hχ hB hG1 hG2
  refine ⟨fun τ i => ?_, fun C _ _ _ _ RC hRC τ i => ?_⟩
  · have h0 : χ τ 0 = 0 := (hχ.2.2.2.2 τ).1
    exact (LocFreeSchanuel.main R 1 (r τ) (D.xId (χ τ) i)
      ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _)) (D.kk τ ((i : ℕ) + 1))
      (D.stepGraph τ (χ τ) i) (((_root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main D R p w χ hχ hB hG1).1 τ).2.2.2 i) (hG2.step τ i)
      (hG2.kk τ _) (stepGraph_stable D hB τ (χ τ) i)
      (fun c m h => ⟨fst_mem_xId_of_mem_stepGraph D hB τ (χ τ) i h, ⟨(c, m), h, rfl⟩⟩)
      (fun c h => exists_mem_stepGraph_of_mem_xId D hB τ (χ τ) h0 i h)
      (zero_mem_stepGraph_iff D τ (χ τ) i)
      (by
        rintro _ ⟨⟨c, m⟩, h, rfl⟩
        exact ⟨c, h⟩)).2
  · have hst := stepGraph_stable D hB τ (χ τ) i
    rw [(_root_.GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change D R p w χ hχ hB hG1 C RC hRC τ).2 i]
    let sw := (AddEquiv.prodComm (M := Ω) (N := Fin (r τ) → Ω)).toAddMonoidHom
    let Δ' : AddSubgroup ((Fin (r τ) → Ω) × Ω) := (D.stepGraph τ (χ τ) i).map sw
    have hst' : ∀ a ∈ R, ∀ v ∈ Δ', a • v ∈ Δ' := by
      rintro a ha _ ⟨x, hx, rfl⟩
      exact ⟨a • x, hst a ha x hx, rfl⟩
    have hfst : Δ'.map (AddMonoidHom.fst _ _) =
        (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) := by
      rw [AddSubgroup.map_map]
      rfl
    have key := (_root_.GlobalTheory.CompanionTheory.Ar.GraphRestrict.main R RC hRC (bcMap Ω C (Fin (r τ))) (Algebra.linearMap Ω C)
      (isBaseChange_bcMap Ω C _) (IsBaseChange.linearMap Ω C) Δ' ⊥ (r τ) hst'
      (hfst ▸ hG2.step τ i) bot_le (by
        intro a _ v hv
        rw [AddSubgroup.mem_bot] at hv ⊢
        rw [hv, smul_zero])).2
    have hsw := spanOver_swap RC (bcMap Ω C (Fin (r τ))) (Algebra.linearMap Ω C)
      (D.stepGraph τ (χ τ) i)
    have e1 : Δ'.comap (AddMonoidHom.inr _ _) =
        (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _) := by
      ext c
      constructor
      · rintro ⟨⟨c', m⟩, h, he⟩
        have h1 : m = 0 := congrArg Prod.fst he
        have h2 : c' = c := congrArg Prod.snd he
        subst h1 h2
        exact h
      · intro h
        exact ⟨_, h, rfl⟩
    have e2 : ∀ X : AddSubgroup (C × (Fin (r τ) → C)),
        (X.map (AddEquiv.prodComm (M := C) (N := Fin (r τ) → C)).toAddMonoidHom).comap
          (AddMonoidHom.inr _ _) = X.comap (AddMonoidHom.inl _ _) := by
      intro X
      ext c
      constructor
      · rintro ⟨⟨c', m⟩, h, he⟩
        have h1 : m = 0 := congrArg Prod.fst he
        have h2 : c' = c := congrArg Prod.snd he
        subst h1 h2
        exact h
      · intro h
        exact ⟨_, h, rfl⟩
    rw [hsw, e2, e1] at key
    exact key

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
end

