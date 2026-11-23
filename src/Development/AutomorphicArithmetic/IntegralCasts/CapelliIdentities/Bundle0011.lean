module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclicTrivialInductionRing
section
private theorem UpperTheory.cyclic_trivial_induction_ring {R : Type} [Ring R] (hR : ∀ c : R, ∃ m : ℤ, c = m) :
    ∀ {H : Type} [Monoid H] (n : ℕ) (P : Rep.{0, 0, 0} R H → Prop),
        (∀ C : Rep.{0, 0, 0} R H, Finite C.V → IsAddCyclic C.V →
          (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) → P C) →
        (∀ (A B C : Rep.{0, 0, 0} R H) (f : A ⟶ B) (g : B ⟶ C),
          (∀ (h : H) (a : A.V), A.ρ h a = a) → (∀ (h : H) (c : C.V), C.ρ h c = c) →
          Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
          P A → P C → P B) →
        ∀ A : Rep.{0, 0, 0} R H, Finite A.V →
          (∀ (g : H) (a : A.V), A.ρ g a = a) → (∀ a : A.V, n • a = 0) → P A := by
  intro H _ n P hcyc hext A
  induction hk : Nat.card A.V using Nat.strong_induction_on generalizing A with
  | _ k ih =>
    intro hfin htriv htors
    by_cases hne : ∃ a : A.V, a ≠ 0
    · obtain ⟨a, ha⟩ := hne
      let B : Submodule R A.V := Submodule.span _ {a}
      let S : Rep.{0, 0, 0} R H := Rep.of (Representation.trivial R H B)
      let Q : Rep.{0, 0, 0} R H :=
        Rep.of (Representation.trivial R H (A.V ⧸ B))
      let f : S ⟶ A := Rep.ofHom (ρ := Representation.trivial R H B) (σ := A.ρ)
        (B.subtype.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
          simpa using (htriv g v.1).symm))
      let g : A ⟶ Q := Rep.ofHom (ρ := A.ρ) (σ := Representation.trivial R H (A.V ⧸ B))
        (B.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
          simp [htriv g v]))
      have hlt : Nat.card (A.V ⧸ B) < Nat.card A.V := by
        by_contra hcon
        have hbij := (Submodule.mkQ_surjective B).bijective_of_nat_card_le (not_lt.mp hcon)
        have hmem : a ∈ B := Submodule.mem_span_singleton_self a
        have h0 : B.mkQ a = B.mkQ 0 := by
          simpa using (Submodule.Quotient.mk_eq_zero B).2 hmem
        exact ha (hbij.1 h0)
      have hS : P S := by
        refine hcyc S (inferInstanceAs (Finite B)) ?_ (fun _ _ => rfl) ?_
        · refine (⟨⟨⟨a, Submodule.mem_span_singleton_self a⟩, fun x => ?_⟩⟩ : IsAddCyclic B)
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
          obtain ⟨m, rfl⟩ := hR c
          refine AddSubgroup.mem_zmultiples_iff.2 ⟨m, Subtype.ext ?_⟩
          rw [← hc, Int.cast_smul_eq_zsmul]
          rfl
        · intro c
          exact Subtype.ext (htors c.1)
      have hQ : P Q := by
        refine ih (Nat.card (A.V ⧸ B)) (hk ▸ hlt) Q rfl
          (Finite.of_surjective B.mkQ (Submodule.mkQ_surjective B))
          (fun _ _ => rfl) ?_
        intro c
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective B c
        have : n • B.mkQ x = B.mkQ (n • x) := (map_nsmul B.mkQ n x).symm
        exact this.trans (by rw [htors x, map_zero])
      exact hext S A Q f g (fun _ _ => rfl) (fun _ _ => rfl) (Subtype.val_injective)
        (LinearMap.exact_subtype_mkQ B) (Submodule.mkQ_surjective B) hS hQ
    · have : Subsingleton A.V := ⟨fun x y => by
        push_neg at hne
        rw [hne x, hne y]⟩
      exact hcyc A hfin inferInstance htriv htors

theorem UpperTheory.cyclic_trivial_induction :
    ∀ {H : Type} [Monoid H] (n : ℕ) (P : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H → Prop),
        (∀ C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H, Finite C.V → IsAddCyclic C.V →
          (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) → P C) →
        (∀ (A B C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) (f : A ⟶ B) (g : B ⟶ C),
          (∀ (h : H) (a : A.V), A.ρ h a = a) → (∀ (h : H) (c : C.V), C.ρ h c = c) →
          Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
          P A → P C → P B) →
        ∀ A : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H, Finite A.V →
          (∀ (g : H) (a : A.V), A.ρ g a = a) → (∀ a : A.V, n • a = 0) → P A := by
  intro H _
  exact UpperTheory.cyclic_trivial_induction_ring (R := ULift.{0, 0} ℤ) (fun c => ⟨c.down, ULift.ext (by simp)⟩)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicBarContinuous
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicBarContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicBarContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicBarContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicBarContinuous.cont_cycBar :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicBarContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have hZ : Continuous (UpperTheory.Reformulated.B.CyclotomicBarContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have hι : Continuous
      (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
        ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicBarContinuous.Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Units.continuous_map hι).comp hZ
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterContinuous
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cont_cyc :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (fun x : ℤ_[l] ↦ algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l])) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterFirst
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G E Ω →* (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp
        (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cyc_continuous :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycBar F Ω l) : UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω → (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous ((algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp PadicInt.Coe.ringHom) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterFourth
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cyc_cont :
    ∀ {E Ω : Type} [inst : Field E] [NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] {l : ℕ}
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycBar E Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.G E Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)ˣ) := by
  intro E Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.cycZ E Ω l) := cyclotomicCharacter.continuous l E Ω
  have h2 : Continuous ((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuity.Qbar l)).comp
      (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l])) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterSecond
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G E Ω →* (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp
        (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar F Ω l) : UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω → (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous
      (((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom :
        ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) : ℤ_[l] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterThird
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) :=
    (algebraMap_isometry ℚ_[l] (PadicAlgCl l)).continuous
  have h3 : Continuous
      (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
        ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l) :=
    h2.comp continuous_subtype_val
  exact (Continuous.units_map _ h3).comp h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwine
section
theorem UpperTheory.Reformulated.B.Qj10.dc_aeval_intertwine.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p y
  have hpow : ∀ (n : ℕ) (x : Y), ψ ((A ^ n) x) = (B ^ n) (ψ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwineAlt
section
theorem UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p
  have hpow : ∀ (n : ℕ) (y : Y), ψ ((A ^ n) y) = (B ^ n) (ψ y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | monomial n a =>
    intro y
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcCons
section
noncomputable def UpperTheory.Reformulated.B.Qj27.dc :
    {Y : Type} → {m : ℕ} → ((Fin (m + (1 : ℕ)) → Y) → ℝ) → (Fin (m + (2 : ℕ)) → Y) → ℝ :=
    fun {Y : Type} {m : ℕ} (F : (Fin (m + (1 : ℕ)) → Y) → ℝ) (y : Fin (m + (2 : ℕ)) → Y) ↦
      ∑ i : Fin (m + (2 : ℕ)), (-1 : ℝ) ^ (↑i : ℕ) * F fun (j : Fin (m + (1 : ℕ))) ↦ y (i.succAbove j)

theorem UpperTheory.Reformulated.B.Qj27.dc_cons :
    ∀ {Y : Type} {m : ℕ} (F : (Fin (m + (2 : ℕ)) → Y) → ℝ) (a : Y) (w : Fin (m + (2 : ℕ)) → Y),
      UpperTheory.Reformulated.B.Qj27.dc F (Fin.cons a w) =
        F w - UpperTheory.Reformulated.B.Qj27.dc (fun (w' : Fin (m + (1 : ℕ)) → Y) ↦ F (Fin.cons a w')) w := by
  intro Y m F a w
  have h : ∀ i : Fin (m + 2),
      (fun j : Fin (m + 2) ↦ (Fin.cons a w : Fin (m + 3) → Y) (i.succ.succAbove j)) =
        (Fin.cons a (fun j : Fin (m + 1) ↦ w (i.succAbove j)) : Fin (m + 2) → Y) := by
    intro i
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp
    · simp
  unfold UpperTheory.Reformulated.B.Qj27.dc
  rw [Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h i, Fin.val_succ, pow_succ]
    ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DegLESum
section
noncomputable def UpperTheory.Reformulated.B.Qf21.degLE :
    {κ R : Type} → [inst : CommRing R] → Finset κ → ℕ → MvPolynomial κ R → Prop :=
    fun {κ R : Type} [CommRing R] (W : Finset κ) (n : ℕ) (F : MvPolynomial κ R) ↦
      ∀ (β : κ →₀ ℕ), AddMonoidAlgebra.coeff F β ≠ (0 : R) → ∑ k ∈ W, (β : κ → ℕ) k ≤ n

theorem UpperTheory.Reformulated.B.Qf21.degLE_sum.{u_1} :
    ∀ {κ R : Type} [inst : CommRing R] {α : Type u_1} {W : Finset κ} {n : ℕ} (s : Finset α) (F : α → MvPolynomial κ R),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf21.degLE W n (F a)) → UpperTheory.Reformulated.B.Qf21.degLE W n (∑ a ∈ s, F a) := by
  intro κ R _ α W n s F h β hβ
  rw [MvPolynomial.coeff_sum] at hβ
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  exact h a ha β hne
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenominatorOfSpan
section
theorem UpperTheory.Reformulated.B.SpanDenominator.den_of_span :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] {i : ℕ} (P : Ideal (NumberField.RingOfIntegers K))
      [inst_2 : P.IsPrime] (M : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      ∀
        x ∈
          Submodule.span ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
            (↑M : Set (Fin i → K)),
        ∃ s ∈ P.primeCompl, s • x ∈ M := by
  intro K _ _ i P _ M x hx
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span P.primeCompl
    ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
    (↑M : Set (Fin i → K)) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, t.2, ht⟩
end

