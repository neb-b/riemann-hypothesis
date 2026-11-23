module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrMap

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TowerGal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem mul_eq_one_of_card_eq_two_of_ne_one {H : Type*} [Group H] (hH : Nat.card H = 2)
    (x y : H) (hx : x ≠ 1) (hy : y ≠ 1) : x * y = 1 := by
  classical
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card] at hH
  by_contra hxy
  have h3 : ({1, x, x * y} : Finset H).card = 3 := by
    refine Finset.card_eq_three.mpr ⟨1, x, x * y, fun h => hx h.symm, fun h => hxy h.symm, ?_, rfl⟩
    intro h
    exact hy (mul_left_cancel (a := x) (by rw [mul_one]; exact h.symm))
  have := Finset.card_le_univ ({1, x, x * y} : Finset H)
  omega

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.Ws.P1.towerGal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), (resLe T.F_le).range = T.GalL ∧ Function.Injective (resLe T.F_le) ∧ Continuous (resLe T.F_le) ∧
          (∀ a b : G T.F Ω, a ∉ T.GalL → b ∉ T.GalL → a * b ∈ T.GalL) ∧
          (∀ g : G T.L Ω, resQ T.F (resLe T.F_le g) = resQ T.L g ∧ cycZ T.F Ω l (resLe T.F_le g) = cycZ T.L Ω l g ∧ cycZ ℚ Ω l (resQ T.L g) = cycZ T.L Ω l g) ∧
          ∀ (A : ValuationSubring Ω) (g : G T.L Ω), (resLe T.F_le g ∈ Dec (F := T.F) A ↔ g ∈ Dec (F := T.L) A) ∧ (resLe T.F_le g ∈ Ine (F := T.F) A ↔ g ∈ Ine (F := T.L) A) := by
  intro Ω _ _ _ l _ c D T
  have hKL : T.K ≤ T.L := by
    rw [T.hL]
    exact le_sup_right
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold UpperTheory.V.Ws.Tower.GalL
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact g.commutes ⟨x, hKL hx⟩
    · intro a ha
      rw [Subgroup.mem_comap] at ha
      have hF : resQ T.F a ∈ T.F.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact a.commutes ⟨x, hx⟩
      have hL : resQ T.F a ∈ T.L.fixingSubgroup := by
        rw [T.hL, IntermediateField.fixingSubgroup_sup]
        exact ⟨hF, ha⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hL
      exact ⟨{ a.toRingEquiv with commutes' := fun x => hL x x.2 }, by ext z; rfl⟩
  · intro g₁ g₂ h
    ext z
    exact congrArg (fun k => k z) h
  · letI : Algebra T.F T.L := (IntermediateField.inclusion T.F_le).toRingHom.toAlgebra
    haveI : IsScalarTower T.F T.L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have he : (resLe T.F_le : G T.L Ω → G T.F Ω) = AlgEquiv.restrictScalarsHom T.F := by
      funext g
      ext
      rfl
    rw [he]
    exact UpperTheory.V.Af.continuous_restrictScalarsHom _ _ _
  · unfold UpperTheory.V.Ws.Tower.GalL
    haveI : Algebra.IsQuadraticExtension ℚ T.K := ⟨T.degK⟩
    haveI hN : Normal ℚ T.K := Algebra.IsQuadraticExtension.normal ℚ T.K
    haveI : IsGalois ℚ T.K := {}
    have hcard : Nat.card (T.K ≃ₐ[ℚ] T.K) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, T.degK]
    have hker := @IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ T.K
      (by convert hN)
    intro a b ha hb
    rw [Subgroup.mem_comap, ← hker, MonoidHom.mem_ker] at ha hb ⊢
    rw [map_mul, map_mul]
    exact mul_eq_one_of_card_eq_two_of_ne_one (by convert hcard <;> first | rfl | exact Subsingleton.elim _ _) _ _ ha hb
  · intro g
    exact ⟨by ext; rfl, rfl, rfl⟩
  · intro A g
    exact ⟨Iff.rfl, Iff.rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TrNe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.trNe :
    ∀ {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H : Subgroup Γ) (χ : Fin (n + 1) → Γ →* kˣ), (Function.Injective fun i => (χ i).comp H.subtype) →
          H = ⊤ ∨ ∃ g, g ∉ H ∧ ∑ i, (χ i g : k) ≠ 0 := by
  intro Γ k _ _ n H χ hinj
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hH, hz⟩ := hcon
  have hz' : ∀ g, g ∉ H → ∑ i, (χ i g : k) = 0 := by
    intro g hg
    by_contra h
    exact hz ⟨g, hg, h⟩
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 ∉ H := by
    by_contra h
    apply hH
    rw [eq_top_iff]
    intro x _
    by_contra hx
    exact h ⟨x, hx⟩
  let ψ : Fin (n + 1) → (H →* k) := fun i => (Units.coeHom k).comp ((χ i).comp H.subtype)
  have hψ : Function.Injective ψ := by
    intro i j hij
    apply hinj
    ext x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom H k).comp ψ hψ
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (fun i => (χ i g0 : k)) (by
    funext h
    have hm : g0 * (h : Γ) ∉ H := fun hm => hg0 ((H.mul_mem_cancel_right h.2).1 hm)
    have := hz' _ hm
    simp only [map_mul, Units.val_mul] at this
    simpa [ψ, Finset.sum_apply] using this) 0
  exact (χ 0 g0).ne_zero h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TraceSwap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open scoped Matrix

private theorem irr_map {Γ E E' : Type} [Group Γ] [Field E] [Field E'] (f : E →+* E') {n : ℕ}
    (r : Γ →* Matrix (Fin n) (Fin n) E) (hr : Irr r) (N : Submodule E' (Fin n → E'))
    (hN : ∀ g, ∀ v ∈ N, (mapRep f r g) *ᵥ v ∈ N) : N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qi38.irr_map f r hr N hN

private theorem trace_swap {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (N M : Submodule K V) (hc : IsCompl N M) (T : Module.End K V)
    (h1 : ∀ v ∈ N, T v ∈ M) (h2 : ∀ v ∈ M, T v ∈ N) : LinearMap.trace K V T = 0 := by
  obtain ⟨p, hpN, hpM⟩ : ∃ p : Module.End K V, (∀ v ∈ N, p v = v) ∧ (∀ v ∈ M, p v = 0) :=
    ⟨N.subtype ∘ₗ N.linearProjOfIsCompl M hc, fun v hv =>
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩),
      fun v hv =>
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨v, hv⟩)⟩
  have key : T = (p * T) * (1 - p) + ((1 - p) * T) * p := by
    ext v
    have hv : v ∈ N ⊔ M := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    simp [hpN a ha, hpM b hb, hpN _ (h2 b hb), hpM _ (h1 a ha), add_comm]
  have hpp : p * p = p := by
    ext v
    have hv : v ∈ N ⊔ M := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    simp [hpN a ha, hpM b hb]
  rw [key, map_add (f := _), LinearMap.trace_mul_comm K (p * T), LinearMap.trace_mul_comm K ((1 - p) * T),
    ← mul_assoc, ← mul_assoc, sub_mul, mul_sub, hpp]
  simp

theorem UpperTheory.V.Ws.P1.irrTr :
    ∀ {Γ E E' : Type} [Group Γ] [Field E] [Field E'] (f : E →+* E') {n : ℕ} (H : Subgroup Γ) (r : Γ →* Matrix (Fin n) (Fin n) E), (2 : E) ≠ 0 → Irr r →
          (∀ a b, a ∉ H → b ∉ H → a * b ∈ H) → (H = ⊤ ∨ ∃ g, g ∉ H ∧ (r g).trace ≠ 0) → U3.MatIrr H (mapRep f r) := by
  intro Γ E E' _ _ _ f n H r _ hr hH hg N hN
  rcases hg with rfl | ⟨g, hg, ht⟩
  · exact irr_map f r hr N fun g => hN g trivial
  set ρ := mapRep f r with hρ
  let M : Submodule E' (Fin n → E') := N.map (Matrix.mulVecLin (ρ g))
  have hNM : ∀ a, a ∉ H → ∀ v ∈ N, ρ a *ᵥ v ∈ M := by
    intro a ha v hv
    have : g⁻¹ * a ∈ H := hH _ _ (fun h => hg (H.inv_mem_iff.1 h)) ha
    refine ⟨_, hN _ this v hv, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel_left]
  have hMN : ∀ a, a ∉ H → ∀ v ∈ M, ρ a *ᵥ v ∈ N := by
    rintro a ha _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul]
    exact hN _ (hH _ _ ha hg) v hv
  have hMM : ∀ a ∈ H, ∀ v ∈ M, ρ a *ᵥ v ∈ M := by
    rintro a ha _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul]
    exact hNM _ (fun h => hg ((H.mul_mem_cancel_left ha).1 h)) v hv
  by_contra hcon
  obtain ⟨hb, htop⟩ := not_or.1 hcon
  have hinf : N ⊓ M = ⊥ := by
    refine (irr_map f r hr (N ⊓ M) fun a v hv => ?_).resolve_right fun h => htop (top_le_iff.1 (h ▸ inf_le_left))
    by_cases ha : a ∈ H
    · exact ⟨hN a ha v hv.1, hMM a ha v hv.2⟩
    · exact ⟨hMN a ha v hv.2, hNM a ha v hv.1⟩
  have hsup : N ⊔ M = ⊤ := by
    refine (irr_map f r hr (N ⊔ M) fun a v hv => ?_).resolve_left fun h => hb (le_bot_iff.1 (h ▸ le_sup_left))
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [Matrix.mulVec_add]
    by_cases ha : a ∈ H
    · exact Submodule.add_mem_sup (hN a ha x hx) (hMM a ha y hy)
    · rw [add_comm]
      exact Submodule.add_mem_sup (hMN a ha y hy) (hNM a ha x hx)
  have hc : IsCompl N M := ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩
  have h0 := trace_swap N M hc (Matrix.toLin' (ρ g)) (fun v hv => hNM g hg v hv) (fun v hv => hMN g hg v hv)
  rw [Matrix.trace_toLin'_eq] at h0
  apply ht
  apply f.injective
  rw [map_zero, ← h0]
  simp [Matrix.trace, hρ]
end

