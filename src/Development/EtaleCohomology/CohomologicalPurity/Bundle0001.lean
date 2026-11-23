module

public import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafCoeqPf
section
noncomputable section
open scoped TensorProduct

namespace LateralTheory.CohomologicalPurity.Hz

theorem coeq_elem {A S S' : Type} [CommRing A] [CommRing S] [CommRing S'] (φ : A →+* S) (φ' : A →+* S')
    (I : Ideal A) (u v : S →+* S') (hφ : Good φ I) (hu : u.comp φ = φ') (hv : v.comp φ = φ') :
    ∃ e : S', (∀ s, (v s - u s) * e = 0) ∧ e - 1 ∈ I.map φ' := by
  let := φ.toAlgebra
  let := φ'.toAlgebra
  have : Algebra.Etale A S := hφ.etale
  let u' : S →ₐ[A] S' := { u with commutes' := fun a => RingHom.congr_fun hu a }
  let v' : S →ₐ[A] S' := { v with commutes' := fun a => RingHom.congr_fun hv a }
  obtain ⟨t, ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := S)).1 inferInstance
  refine ⟨Algebra.TensorProduct.productMap u' v' t, fun s => ?_, ?_⟩
  · have h := congrArg (Algebra.TensorProduct.productMap u' v') (ht1 s)
    simpa [map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul, u', v'] using h
  · have hmem : ∀ x ∈ I.map φ, u x ∈ I.map φ' ∧ v x ∈ I.map φ' := fun x hx => by
      refine ⟨?_, ?_⟩
      · have := Ideal.mem_map_of_mem u hx
        rwa [Ideal.map_map, hu] at this
      · have := Ideal.mem_map_of_mem v hx
        rwa [Ideal.map_map, hv] at this
    let q := Ideal.Quotient.mkₐ A (I.map φ')
    have hqv : q.comp v' = q.comp u' := by
      ext s
      obtain ⟨a, ha⟩ := hφ.surj s
      have e1 : v s - u s = v (s - φ a) - u (s - φ a) := by
        have h1 : v (φ a) = u (φ a) := (RingHom.congr_fun hv a).trans (RingHom.congr_fun hu a).symm
        rw [map_sub, map_sub, h1]; ring
      change Ideal.Quotient.mk _ (v s) = Ideal.Quotient.mk _ (u s)
      rw [Ideal.Quotient.eq, e1]
      exact Ideal.sub_mem _ (hmem _ ha).2 (hmem _ ha).1
    have hprod : q.comp (Algebra.TensorProduct.productMap u' v') = q.comp (u'.comp (Algebra.TensorProduct.lmul' A)) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      have hb := AlgHom.congr_fun hqv b
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul,
        Algebra.TensorProduct.lmul'_apply_tmul] at hb ⊢
      rw [hb]
    have h := AlgHom.congr_fun hprod t
    simp only [AlgHom.comp_apply] at h
    rw [ht2, map_one] at h
    rw [← Ideal.Quotient.eq]
    simpa [q] using h

theorem LeafCoeq_of (hInv : LeafInv) (hComp : LeafComp) : LeafCoeq := by
  intro A S S' _ _ _ φ φ' I u v hφ hφ' hu hv
  obtain ⟨e, he1, he2⟩ := coeq_elem φ φ' I u v hφ hu hv
  obtain ⟨T, _, ψ, hg, hunit⟩ := hInv S' (I.map φ') (e - 1) he2
  rw [add_sub_cancel] at hunit
  refine ⟨T, inferInstance, ψ, RingHom.ext fun s => ?_, hComp.2 A S' T φ' ψ I hφ' hg⟩
  have h := congrArg ψ (he1 s)
  rw [map_mul, map_zero, hunit.mul_left_eq_zero, map_sub, sub_eq_zero] at h
  exact h.symm

end LateralTheory.CohomologicalPurity.Hz
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafColHensPf
section
noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

theorem evalMapHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X]) (x : R) :
    (p.map f).eval (f x) = f (p.eval x) := by
  rw [eval_map, eval₂_at_apply]

theorem Diag.leg_comp_map {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) {j k : Δ.J}
    (e : j ⟶ k) : (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j :=
  congrArg CommRingCat.Hom.hom (c.w e)

theorem LeafColHens_of (hS : LeafStage) (hI : LeafInv) (hR : LeafRoot) : LeafColHens := by
  classical
  intro A _ I Δ c hc η hη
  have st := hS A I Δ c hc η hη
  have push : ∀ j (S : Type) [CommRing S] (φ : Δ.D.obj j →+* S), Good φ (I.map (Δ.s j)) →
      ∃ π : S →+* c.pt, π.comp φ = Δ.leg c j := by
    intro j S _ φ hφ
    obtain ⟨k, e, ρ, hρ⟩ := Δ.exh j S φ hφ
    exact ⟨(Δ.leg c k).comp ρ, by rw [RingHom.comp_assoc, hρ, Δ.leg_comp_map]⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Ring.mem_jacobson_iff]
    intro y
    have hzy : z * y ∈ I.map η := Ideal.mul_mem_right y _ hz
    obtain ⟨j, hj⟩ := st.1 {z * y}
    obtain ⟨x, hx⟩ := hj (z * y) (Finset.mem_singleton_self _)
    have hx' : x ∈ I.map (Δ.s j) := st.2 j x (by rw [hx]; exact hzy)
    obtain ⟨S, _, φ, hφ, hu⟩ := hI (Δ.D.obj j) (I.map (Δ.s j)) x hx'
    obtain ⟨π, hπ⟩ := push j S φ hφ
    have h := hu.map π
    rw [← RingHom.comp_apply, hπ, map_add (f := _), map_one, hx, add_comm] at h
    exact h
  · intro f hf a₀ ha₀ hu
    obtain ⟨u, hu'⟩ := Ideal.Quotient.mk_surjective (↑hu.unit⁻¹ : c.pt ⧸ I.map η)
    have hdu : f.derivative.eval a₀ * u - 1 ∈ I.map η := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu', map_one, IsUnit.mul_val_inv, sub_self]
    let T : Finset c.pt := insert a₀ (insert u (f.support.image f.coeff))
    obtain ⟨j, hj⟩ := st.1 T
    obtain ⟨a, ha⟩ := hj a₀ (Finset.mem_insert_self _ _)
    obtain ⟨v, hv⟩ := hj u (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hco : ∀ n, f.coeff n ∈ Set.range (Δ.leg c j) := by
      intro n
      by_cases hn : n ∈ f.support
      · exact hj _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn)))
      · exact ⟨0, by rw [map_zero, notMem_support_iff.1 hn]⟩
    obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts f).2 hco) hf
    have h1 : g.eval a ∈ I.map (Δ.s j) := st.2 j _ (by rw [← evalMapHom, hg, ha]; exact ha₀)
    have h2 : g.derivative.eval a * v - 1 ∈ I.map (Δ.s j) := st.2 j _ (by
      rw [map_sub, map_mul, map_one, ← evalMapHom, ← derivative_map, hg, ha, hv]; exact hdu)
    have h3 : IsUnit (Ideal.Quotient.mk (I.map (Δ.s j)) (g.derivative.eval a)) :=
      IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ v)
        (by rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.map (Δ.s j)))]; exact Ideal.Quotient.eq.2 h2)
    obtain ⟨S, _, φ, b, hφ, hb, hba⟩ := hR (Δ.D.obj j) (I.map (Δ.s j)) g a hgm h1 h3
    obtain ⟨π, hπ⟩ := push j S φ hφ
    refine ⟨π b, ?_, ?_⟩
    · have h := hb.map (f := π)
      rwa [Polynomial.map_map, hπ, hg] at h
    · have h := Ideal.mem_map_of_mem π hba
      rw [Ideal.map_map, Ideal.map_map, hπ, hη, map_sub, ← RingHom.comp_apply, hπ, ha] at h
      exact h

end LateralTheory.CohomologicalPurity.Hz
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafColUnivPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem LeafColUniv_of : LeafColUniv := by
  intro A _ I Δ c hc η hη B _ J hJ ψ hψ
  have hu : ∀ j, ∃! χ : Δ.D.obj j →+* B, χ.comp (Δ.s j) = ψ := fun j => (Δ.good j).univ B J hJ ψ hψ
  choose χ hχ hχu using hu
  have hnat : ∀ {j k : Δ.J} (e : j ⟶ k), (χ k).comp (Δ.D.map e).hom = χ j := fun {j k} e => by
    apply hχu j
    rw [RingHom.comp_assoc, Δ.nat e, hχ k]
  let cB : Cocone Δ.D := ⟨CommRingCat.of B, ⟨fun j => CommRingCat.ofHom (χ j), fun j k e => by
    apply CommRingCat.hom_ext
    simpa using hnat e⟩⟩
  let d := hc.desc cB
  have hfac : ∀ j, d.hom.comp (Δ.leg c j) = χ j := fun j => by
    have := hc.fac cB j
    exact congrArg CommRingCat.Hom.hom this
  obtain ⟨j₀⟩ : Nonempty Δ.J := IsFiltered.nonempty
  refine ⟨d.hom, ?_, fun χ' h' => ?_⟩
  · show d.hom.comp η = ψ
    rw [← hη j₀, ← RingHom.comp_assoc, hfac, hχ]
  · have h2 : ∀ j, χ'.comp (Δ.leg c j) = χ j := fun j => by
      apply hχu j
      rw [RingHom.comp_assoc, hη j, h']
    have : CommRingCat.ofHom χ' = d := hc.hom_ext fun j => by
      apply CommRingCat.hom_ext
      change χ'.comp (Δ.leg c j) = d.hom.comp (Δ.leg c j)
      rw [h2, hfac]
    rw [← this]
    rfl

end LateralTheory.CohomologicalPurity.Hz
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafCompPf
section
noncomputable section

namespace LateralTheory.CohomologicalPurity.Hz

theorem good_iso (A S : Type) [CommRing A] [CommRing S] (e : A ≃+* S) (I : Ideal A) : Good (e : A →+* S) I := by
  refine ⟨RingHom.Etale.of_bijective e.bijective, ⟨(Ideal.Quotient.mk I).comp (e.symm : S →+* A), ?_⟩, fun s => ⟨e.symm s, ?_⟩, ?_⟩
  · ext a; simp
  · simp
  · intro B _ J _ ψ _
    refine ⟨ψ.comp (e.symm : S →+* A), ?_, fun χ hχ => ?_⟩
    · ext a; simp
    · ext s
      have := congrArg (fun f : A →+* B => f (e.symm s)) hχ
      simpa using this

theorem good_comp (A S T : Type) [CommRing A] [CommRing S] [CommRing T] (φ : A →+* S) (ψ : S →+* T) (I : Ideal A)
    (h1 : Good φ I) (h2 : Good ψ (I.map φ)) : Good (ψ.comp φ) I := by
  obtain ⟨r1, hr1⟩ := h1.retr
  obtain ⟨r2, hr2⟩ := h2.retr
  have hk : I.map φ ≤ RingHom.ker r1 := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change (r1.comp φ) a = 0
    rw [hr1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha
  refine ⟨RingHom.Etale.stableUnderComposition φ ψ h1.etale h2.etale,
    ⟨(Ideal.Quotient.lift (I.map φ) r1 (fun a ha => hk ha)).comp r2, ?_⟩, fun t => ?_, ?_⟩
  · ext a
    have e2 : r2 (ψ (φ a)) = Ideal.Quotient.mk (I.map φ) (φ a) := congrArg (fun f : S →+* S ⧸ I.map φ => f (φ a)) hr2
    simp only [RingHom.comp_apply, e2, Ideal.Quotient.lift_mk]
    exact congrArg (fun f : A →+* A ⧸ I => f a) hr1
  · obtain ⟨s, hs⟩ := h2.surj t
    obtain ⟨a, ha⟩ := h1.surj s
    refine ⟨a, ?_⟩
    rw [Ideal.map_map] at hs
    have h3 : ψ (s - φ a) ∈ (I.map φ).map ψ := Ideal.mem_map_of_mem ψ ha
    rw [Ideal.map_map] at h3
    have : t - (ψ.comp φ) a = (t - ψ s) + ψ (s - φ a) := by simp [map_sub]
    rw [this]
    exact Ideal.add_mem _ hs h3
  · intro B _ J hB χ0 hI
    obtain ⟨χ1, hχ1, hu1⟩ := h1.univ B J hB χ0 hI
    have hI2 : I.map φ ≤ J.comap χ1 := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hχ1]
      exact hI
    obtain ⟨χ2, hχ2, hu2⟩ := h2.univ B J hB χ1 hI2
    refine ⟨χ2, ?_, fun χ hχ => ?_⟩
    · show χ2.comp (ψ.comp φ) = χ0
      rw [← RingHom.comp_assoc, hχ2, hχ1]
    · apply hu2
      apply hu1
      show (χ.comp ψ).comp φ = χ0
      rw [RingHom.comp_assoc]
      exact hχ

theorem LeafComp_of : LeafComp := ⟨good_iso, good_comp⟩

end LateralTheory.CohomologicalPurity.Hz
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRootPf
section
noncomputable section
open Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

def LeafRootStd : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (f : A[X]) (a : A), f.Monic → f.eval a ∈ I →
  IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) →
  ∃ (S : Type) (_ : CommRing S) (φ : A →+* S) (b : S), φ.Etale ∧
    (∃ r : S →+* A ⧸ I, r.comp φ = Ideal.Quotient.mk I) ∧ (∀ s : S, ∃ a' : A, s - φ a' ∈ I.map φ) ∧
    (f.map φ).IsRoot b ∧ b - φ a ∈ I.map φ ∧
    (∀ (B : Type) [CommRing B] (χ₁ χ₂ : S →+* B), χ₁.comp φ = χ₂.comp φ → χ₁ b = χ₂ b → χ₁ = χ₂) ∧
    (∀ (B : Type) [CommRing B] (ψ : A →+* B) (c : B), (f.map ψ).IsRoot c →
      IsUnit ((f.derivative.map ψ).eval c) → IsUnit (((f /ₘ (X - C a)).map ψ).eval c) →
      ∃ χ : S →+* B, χ.comp φ = ψ ∧ χ b = c)

def LeafRootHens : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B), HenselianRing B J →
  ∀ (ψ : A →+* B), I ≤ J.comap ψ → ∀ (f : A[X]) (a : A), f.Monic → f.eval a ∈ I →
  IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) →
  ∃ c : B, (f.map ψ).IsRoot c ∧ c - ψ a ∈ J ∧ IsUnit ((f.derivative.map ψ).eval c) ∧
    IsUnit (((f /ₘ (X - C a)).map ψ).eval c) ∧ ∀ c' : B, (f.map ψ).IsRoot c' → c' - ψ a ∈ J → c' = c

theorem LeafRoot_of (h1 : LeafRootStd) (h2 : LeafRootHens) : LeafRoot := by
  intro A _ I f a hf hfa hu
  obtain ⟨S, _, φ, b, he, hr, hs, hb, hba, hext, hlift⟩ := h1 A I f a hf hfa hu
  refine ⟨S, inferInstance, φ, b, ⟨he, hr, hs, ?_⟩, hb, hba⟩
  intro B _ J hJ ψ hIJ
  obtain ⟨c, hc, _, hc1, hc2, huniq⟩ := h2 A B I J hJ ψ hIJ f a hf hfa hu
  obtain ⟨χ, hχ, hχb⟩ := hlift B ψ c hc hc1 hc2
  refine ⟨χ, hχ, fun χ' hχ' => hext B χ' χ (hχ'.trans hχ.symm) ?_⟩
  rw [hχb]
  have hpa : χ' (φ a) = ψ a := by rw [← hχ']; rfl
  apply huniq
  · have h4 : (f.map φ).map χ' = f.map ψ := by rw [Polynomial.map_map, hχ']
    rw [← h4]
    exact Polynomial.IsRoot.map χ' hb
  · have h3 : (I.map φ).map χ' ≤ J := by
      rw [Ideal.map_map, hχ', Ideal.map_le_iff_le_comap]; exact hIJ
    have h5 := h3 (Ideal.mem_map_of_mem χ' hba)
    rwa [map_sub, hpa] at h5

end LateralTheory.CohomologicalPurity.Hz
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafStagePf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem Diag.leg_w {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) {j k : Δ.J} (e : j ⟶ k) :
    (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j :=
  congrArg CommRingCat.Hom.hom (c.w e)

theorem Good.kill {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A}
    (ψ : S →+* A ⧸ I) (hψ : ψ.comp φ = Ideal.Quotient.mk I) : ∀ y ∈ I.map φ, ψ y = 0 := by
  intro y hy
  have h : I.map φ ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change ψ (φ a) = 0
    rw [← RingHom.comp_apply, hψ]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha
  exact h hy

theorem Good.retr_unique {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A} (h : Good φ I)
    (χ χ' : S →+* A ⧸ I) (hχ : χ.comp φ = Ideal.Quotient.mk I) (hχ' : χ'.comp φ = Ideal.Quotient.mk I) : χ = χ' := by
  refine RingHom.ext fun s => ?_
  obtain ⟨a, ha⟩ := h.surj s
  have e1 := Good.kill χ hχ _ ha
  have e2 := Good.kill χ' hχ' _ ha
  rw [map_sub, sub_eq_zero] at e1 e2
  rw [e1, e2, ← RingHom.comp_apply, hχ, ← RingHom.comp_apply, hχ']

theorem stage_fin {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) (hc : IsColimit c)
    (T : Finset c.pt) : ∃ j, ∀ t ∈ T, t ∈ (Δ.leg c j).range := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨(IsFiltered.nonempty : Nonempty Δ.J).some, by simp⟩
  | insert x T hx ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, y, hy⟩ := Concrete.isColimit_exists_rep Δ.D hc x
    refine ⟨IsFiltered.max j k, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · refine ⟨(Δ.D.map (IsFiltered.rightToMax j k)).hom y, ?_⟩
      rw [← RingHom.comp_apply, Δ.leg_w]
      exact hy
    · obtain ⟨z, rfl⟩ := hj t ht
      exact ⟨(Δ.D.map (IsFiltered.leftToMax j k)).hom z, by rw [← RingHom.comp_apply, Δ.leg_w]⟩

theorem stage_ideal {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) (hc : IsColimit c)
    (η : A →+* c.pt) (hη : ∀ j, (Δ.leg c j).comp (Δ.s j) = η) (j : Δ.J) (x : Δ.D.obj j)
    (hx : Δ.leg c j x ∈ I.map η) : x ∈ I.map (Δ.s j) := by
  let r : ∀ j, Δ.D.obj j →+* A ⧸ I := fun j => (Δ.good j).retr.choose
  have hr : ∀ j, (r j).comp (Δ.s j) = Ideal.Quotient.mk I := fun j => (Δ.good j).retr.choose_spec
  let cc : Cocone Δ.D :=
    { pt := CommRingCat.of (A ⧸ I)
      ι := { app := fun j => CommRingCat.ofHom (r j)
             naturality := fun j k e => by
               apply CommRingCat.hom_ext
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, CommRingCat.hom_comp,
                 CommRingCat.hom_ofHom]
               exact (Δ.good j).retr_unique _ _ (by rw [RingHom.comp_assoc, Δ.nat e, hr]) (hr j) } }
  let R : c.pt →+* A ⧸ I := (hc.desc cc).hom
  have hR : ∀ j, R.comp (Δ.leg c j) = r j := fun j => congrArg CommRingCat.Hom.hom (hc.fac cc j)
  have hRη : R.comp η = Ideal.Quotient.mk I := by rw [← hη j, ← RingHom.comp_assoc, hR, hr]
  obtain ⟨a, ha⟩ := (Δ.good j).surj x
  have h1 : Δ.leg c j (x - Δ.s j a) ∈ I.map η := by
    have := Ideal.mem_map_of_mem (Δ.leg c j) ha
    rwa [Ideal.map_map, hη] at this
  have h2 : η a ∈ I.map η := by
    have e : η a = Δ.leg c j x - Δ.leg c j (x - Δ.s j a) := by
      rw [map_sub, sub_sub_cancel, ← RingHom.comp_apply, hη]
    rw [e]
    exact Ideal.sub_mem _ hx h1
  have h3 : Ideal.Quotient.mk I a = 0 := by
    rw [← Good.kill R hRη _ h2, ← RingHom.comp_apply, hRη]
  have haI : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 h3
  have e : x = (x - Δ.s j a) + Δ.s j a := by ring
  rw [e]
  exact Ideal.add_mem _ ha (Ideal.mem_map_of_mem _ haI)

theorem LeafStage_of : LeafStage := fun _ _ _ Δ c hc η hη =>
  ⟨stage_fin Δ c hc, stage_ideal Δ c hc η hη⟩

end LateralTheory.CohomologicalPurity.Hz
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafSupPf
section
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.Hz

section Sup
variable {A S S' : Type} [CommRing A] [CommRing S] [CommRing S'] [Algebra A S] [Algebra A S'] (I : Ideal A)

theorem sup_etale (h : (algebraMap A S).Etale) (h' : (algebraMap A S').Etale) :
    (algebraMap A (S ⊗[A] S')).Etale := by
  rw [RingHom.etale_algebraMap] at *
  exact Algebra.Etale.comp A S (S ⊗[A] S')

theorem sup_retr (hr : ∃ r : S →+* A ⧸ I, r.comp (algebraMap A S) = Ideal.Quotient.mk I)
    (hr' : ∃ r : S' →+* A ⧸ I, r.comp (algebraMap A S') = Ideal.Quotient.mk I) :
    ∃ r : S ⊗[A] S' →+* A ⧸ I, r.comp (algebraMap A (S ⊗[A] S')) = Ideal.Quotient.mk I := by
  obtain ⟨r, hr⟩ := hr
  obtain ⟨r', hr'⟩ := hr'
  have c1 : ∀ a, r (algebraMap A S a) = algebraMap A (A ⧸ I) a := fun a => by
    rw [Ideal.Quotient.algebraMap_eq]; exact RingHom.congr_fun hr a
  have c2 : ∀ a, r' (algebraMap A S' a) = algebraMap A (A ⧸ I) a := fun a => by
    rw [Ideal.Quotient.algebraMap_eq]; exact RingHom.congr_fun hr' a
  let f : S →ₐ[A] A ⧸ I := { r with commutes' := c1 }
  let g : S' →ₐ[A] A ⧸ I := { r' with commutes' := c2 }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_⟩
  ext a
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq]

theorem mem_map_of_algHom {B : Type} [CommRing B] [Algebra A B] (f : S →ₐ[A] B) {s : S} {a : A}
    (h : s - algebraMap A S a ∈ I.map (algebraMap A S)) : f s - algebraMap A B a ∈ I.map (algebraMap A B) := by
  have e : (f : S →+* B).comp (algebraMap A S) = algebraMap A B := f.comp_algebraMap
  have h2 := Ideal.mem_map_of_mem (f : S →+* B) h
  rw [Ideal.map_map, e, map_sub] at h2
  simpa using h2

theorem sup_surj (hs : ∀ s : S, ∃ a : A, s - algebraMap A S a ∈ I.map (algebraMap A S))
    (hs' : ∀ s : S', ∃ a : A, s - algebraMap A S' a ∈ I.map (algebraMap A S')) (t : S ⊗[A] S') :
    ∃ a : A, t - algebraMap A (S ⊗[A] S') a ∈ I.map (algebraMap A (S ⊗[A] S')) := by
  set J := I.map (algebraMap A (S ⊗[A] S'))
  let R : Subring ((S ⊗[A] S') ⧸ J) := ((Ideal.Quotient.mk J).comp (algebraMap A (S ⊗[A] S'))).range
  have key : ∀ {B : Type} [CommRing B] [Algebra A B]
      (_ : ∀ s : B, ∃ a : A, s - algebraMap A B a ∈ I.map (algebraMap A B)) (f : B →ₐ[A] S ⊗[A] S') (s : B),
      Ideal.Quotient.mk J (f s) ∈ R := by
    intro B _ _ hB f s
    obtain ⟨a, ha⟩ := hB s
    refine ⟨a, ?_⟩
    show Ideal.Quotient.mk J (algebraMap A _ a) = Ideal.Quotient.mk J (f s)
    exact (Ideal.Quotient.eq.2 (mem_map_of_algHom I f ha)).symm
  suffices Ideal.Quotient.mk J t ∈ R by
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Ideal.Quotient.eq.1 ha.symm⟩
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact R.zero_mem
  | tmul s s' =>
    have e : s ⊗ₜ[A] s' = Algebra.TensorProduct.includeLeft (S := A) s * Algebra.TensorProduct.includeRight s' := by
      simp
    rw [e, map_mul]
    exact R.mul_mem (key hs _ s) (key hs' _ s')
  | add x y hx hy => rw [map_add (f := _)]; exact R.add_mem hx hy

theorem sup_univ (hu : Univ (algebraMap A S) I) (hu' : Univ (algebraMap A S') I) :
    Univ (algebraMap A (S ⊗[A] S')) I := by
  intro B _ J hB ψ hIJ
  let _ : Algebra A B := ψ.toAlgebra
  obtain ⟨χ, hχ, -⟩ := hu B J hB ψ hIJ
  obtain ⟨χ', hχ', -⟩ := hu' B J hB ψ hIJ
  let f : S →ₐ[A] B := { χ with commutes' := fun a => RingHom.congr_fun hχ a }
  let g : S' →ₐ[A] B := { χ' with commutes' := fun a => RingHom.congr_fun hχ' a }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_, ?_⟩
  · ext a
    exact (Algebra.TensorProduct.productMap f g).commutes a
  · intro χ₁ h₁
    have hl : χ₁.comp (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S') : S →ₐ[A] S ⊗[A] S').toRingHom = χ := by
      refine (hu B J hB ψ hIJ).unique ?_ hχ
      rw [RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, h₁]
    have hr : χ₁.comp (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := S') : S' →ₐ[A] S ⊗[A] S').toRingHom = χ' := by
      refine (hu' B J hB ψ hIJ).unique ?_ hχ'
      rw [RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, h₁]
    refine RingHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s s' =>
      have e : s ⊗ₜ[A] s' = Algebra.TensorProduct.includeLeft (S := A) s * Algebra.TensorProduct.includeRight s' := by
        simp
      rw [e, map_mul, map_mul]
      have a1 := RingHom.congr_fun hl s
      have a2 := RingHom.congr_fun hr s'
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at a1 a2
      rw [a1, a2]
      simp [f, g]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sup_good (h : Good (algebraMap A S) I) (h' : Good (algebraMap A S') I) :
    Good (algebraMap A (S ⊗[A] S')) I :=
  ⟨sup_etale h.etale h'.etale, sup_retr I h.retr h'.retr, sup_surj I h.surj h'.surj, sup_univ I h.univ h'.univ⟩

end Sup

theorem LeafSup_of : LeafSup := by
  intro A S S' _ _ _ φ φ' I h h'
  let _ : Algebra A S := φ.toAlgebra
  let _ : Algebra A S' := φ'.toAlgebra
  refine ⟨S ⊗[A] S', inferInstance, (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S') : S →ₐ[A] S ⊗[A] S').toRingHom,
    (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := S') : S' →ₐ[A] S ⊗[A] S').toRingHom, ?_, ?_⟩
  · exact RingHom.ext fun a => ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S')).commutes a).trans
      ((Algebra.TensorProduct.includeRight (R := A) (A := S) (B := S')).commutes a).symm
  · have e : (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S') : S →ₐ[A] S ⊗[A] S').toRingHom.comp φ =
        algebraMap A (S ⊗[A] S') :=
      RingHom.ext fun a => (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := S')).commutes a
    rw [e]
    exact sup_good I h h'

end LateralTheory.CohomologicalPurity.Hz
end
end

