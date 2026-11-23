module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcNeg
section
open UpperTheory.V.FW

private theorem div_sub_add_div_add_one_eq (c M a : ℕ) (hM : 0 < M) (hr : a % M ≠ 0) (ha : a < c * M) :
    (c * M - a) / M + a / M + 1 = c := by
  have hdm := Nat.div_add_mod a M
  have hrl := Nat.mod_lt a hM
  generalize a / M = k at hdm ⊢
  generalize a % M = r at hdm hrl hr
  subst hdm
  have hkc : k < c := by
    by_contra hck
    push_neg at hck
    have : M * c ≤ M * k := Nat.mul_le_mul_left M hck
    nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, c = k + 1 + j := ⟨c - k - 1, by omega⟩
  have e1 : (k + 1 + j) * M = M * k + M + j * M := by ring
  have hq : ((k + 1 + j) * M - (M * k + r)) / M = j := by
    apply Nat.div_eq_of_lt_le
    · rw [e1]
      omega
    · rw [e1, Nat.add_mul, Nat.one_mul]
      omega
  rw [hq]
  omega

theorem UpperTheory.V.FW.gcNeg :
    ∀ (M c : ℕ) [NeZero M] (s : ZMod M), c.Coprime M → Odd c → s ≠ 0 → gc M c (-s) = -gc M c s := by
  intro M c _ s hc hodd hs
  unfold gc
  have hcu : IsUnit (c : ZMod M) := (ZMod.isUnit_iff_coprime c M).mpr hc
  have ht : (c : ZMod M)⁻¹ * -s = -((c : ZMod M)⁻¹ * s) := by ring
  have ht0 : (c : ZMod M)⁻¹ * s ≠ 0 := by
    intro h0
    apply hs
    calc s = ((c : ZMod M) * (c : ZMod M)⁻¹) * s := by rw [ZMod.mul_inv_of_unit _ hcu, one_mul]
      _ = (c : ZMod M) * ((c : ZMod M)⁻¹ * s) := by ring
      _ = 0 := by rw [h0, mul_zero]
  haveI : NeZero ((c : ZMod M)⁻¹ * s) := ⟨ht0⟩
  rw [ht, ZMod.val_neg_of_ne_zero]
  have hv0 : 0 < ((c : ZMod M)⁻¹ * s).val := ZMod.val_pos.mpr ht0
  have hvM : ((c : ZMod M)⁻¹ * s).val < M := ZMod.val_lt _
  generalize ((c : ZMod M)⁻¹ * s).val = v at hv0 hvM ⊢
  have hMpos : 0 < M := by omega
  have hcpos : 0 < c := hodd.pos
  have hndvd : (c * v) % M ≠ 0 := by
    intro h0
    have h1 : M ∣ c * v := Nat.dvd_of_mod_eq_zero h0
    have h2 : M ∣ v := (Nat.Coprime.dvd_mul_left hc.symm).mp h1
    have := Nat.le_of_dvd hv0 h2
    omega
  have hlt : c * v < c * M := Nat.mul_lt_mul_of_pos_left hvM hcpos
  have key := div_sub_add_div_add_one_eq c M (c * v) hMpos hndvd hlt
  rw [mul_tsub]
  obtain ⟨m, rfl⟩ := hodd
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm]
  generalize ((2 * m + 1) * M - (2 * m + 1) * v) / M = P at key ⊢
  generalize (2 * m + 1) * v / M = Q at key ⊢
  push_cast
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HomLe
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.homLe :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (U : Subgroup Γ) [U.FiniteIndex], Finite {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0} ∧ Nat.card {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0} ≤ U.index := by
  intro l _ Γ _ U _
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have h1 : ∀ φ : Γ → ZMod l, (∀ a b, φ (a * b) = φ a + φ b) → φ 1 = 0 := by
    intro φ hφ
    have := hφ 1 1
    simp only [mul_one] at this
    simpa using this
  have hc : ∀ φ : Γ → ZMod l, (∀ a b, φ (a * b) = φ a + φ b) → (∀ u ∈ U, φ u = 0) →
      ∀ a b : Γ, a⁻¹ * b ∈ U → φ a = φ b := by
    intro φ hφ hU a b hab
    have := hφ a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hU _ hab, add_zero] at this
    exact this.symm
  let S : Submodule (ZMod l) (Γ → ZMod l) :=
    { carrier := {φ | (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0}
      add_mem' := by
        rintro φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
        refine ⟨fun a b => ?_, fun u hu => ?_⟩
        · simp only [Pi.add_apply, h1, h3]
          ring
        · simp [h2 u hu, h4 u hu]
      zero_mem' := ⟨fun a b => by simp, fun u hu => rfl⟩
      smul_mem' := by
        rintro c φ ⟨h1, h2⟩
        refine ⟨fun a b => ?_, fun u hu => ?_⟩
        · simp only [Pi.smul_apply, h1, smul_eq_mul]
          ring
        · simp [h2 u hu] }
  have hinj : Function.Injective (fun φ : S => fun q : Γ ⧸ U => (φ : Γ → ZMod l) q.out) := by
    intro φ ψ h
    apply Subtype.ext
    funext g
    have e := congrFun h (g : Γ ⧸ U)
    have hg : (Quotient.out (g : Γ ⧸ U))⁻¹ * g ∈ U := by
      rw [← QuotientGroup.eq]
      simp
    simp only at e
    rw [← hc _ φ.2.1 φ.2.2 _ _ hg, ← hc _ ψ.2.1 ψ.2.2 _ _ hg]
    exact e
  haveI : Finite S := Finite.of_injective _ hinj
  change Finite S ∧ Nat.card S ≤ U.index
  refine ⟨inferInstance, ?_⟩
  haveI : FiniteDimensional (ZMod l) S := Module.Finite.of_finite
  let ev : Γ → Module.Dual (ZMod l) S := fun g =>
    { toFun := fun φ => (φ : Γ → ZMod l) g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ a b : Γ, a⁻¹ * b ∈ U → ev a = ev b := by
    intro a b hab
    ext φ
    exact hc _ φ.2.1 φ.2.2 a b hab
  let A : AddSubgroup (Module.Dual (ZMod l) S) :=
    { carrier := Set.range ev
      zero_mem' := ⟨1, by ext φ; exact h1 _ φ.2.1⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, by ext φ; exact φ.2.1 a b⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        refine ⟨a⁻¹, ?_⟩
        ext φ
        have e := φ.2.1 a⁻¹ a
        rw [inv_mul_cancel, h1 _ φ.2.1] at e
        exact eq_neg_of_add_eq_zero_left e.symm }
  have htop : AddSubgroup.toZModSubmodule l A = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    obtain ⟨φ, rfl⟩ := (Module.evalEquiv (ZMod l) S).surjective f
    have hφ : φ = 0 := by
      apply Subtype.ext
      funext g
      have := hle (show ev g ∈ AddSubgroup.toZModSubmodule l A from ⟨g, rfl⟩)
      simpa [ev] using this
    simp [hφ]
  have hsurj : Function.Surjective ev := by
    intro f
    have : f ∈ AddSubgroup.toZModSubmodule l A := by rw [htop]; trivial
    exact this
  have hq : Function.Surjective (fun q : Γ ⧸ U => ev q.out) := by
    intro f
    obtain ⟨g, rfl⟩ := hsurj f
    refine ⟨(g : Γ ⧸ U), ?_⟩
    apply hev
    rw [← QuotientGroup.eq]
    simp
  have e1 : Nat.card S = Nat.card (Module.Dual (ZMod l) S) :=
    Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq.symm).toEquiv
  rw [e1]
  exact Nat.card_le_card_of_surjective _ hq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.NilCard
section
open UpperTheory.V.FW

private theorem card_le_card_ker_mul_card_map {V : Type} [AddCommGroup V] [Finite V] (f : V →+ V)
    (H : AddSubgroup V) :
    Nat.card H ≤ Nat.card (AddMonoidHom.ker f) * Nat.card (H.map f) := by
  set g : H →+ V := f.comp H.subtype with hg
  have h1 := AddSubgroup.card_mul_index (AddMonoidHom.ker g)
  rw [AddSubgroup.index_ker] at h1
  have h2 : AddMonoidHom.range g = H.map f := by
    rw [hg, ← AddMonoidHom.map_range, AddSubgroup.range_subtype]
  have h3 : Nat.card (AddMonoidHom.ker g) ≤ Nat.card (AddMonoidHom.ker f) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : V), by
        have hx := x.2
        rw [AddMonoidHom.mem_ker] at hx ⊢
        exact hx⟩ : AddMonoidHom.ker f)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hab
  rw [← h1, h2]
  exact Nat.mul_le_mul_right _ h3

theorem UpperTheory.V.FW.nilCard :
    ∀ (V : Type) [AddCommGroup V] [Finite V] (T : AddMonoid.End V) (N : ℕ), T ^ N = 0 → Nat.card V ≤ (AddMonoidHom.range T).index ^ N := by
  intro V _ _ T N hN
  set K := Nat.card (AddMonoidHom.ker (T : V →+ V)) with hK
  have hidx : (AddMonoidHom.range (T : V →+ V)).index = K := by
    have a := AddSubgroup.card_mul_index (AddMonoidHom.ker (T : V →+ V))
    have c := AddSubgroup.index_ker (T : V →+ V)
    rw [c] at a
    have b := AddSubgroup.card_mul_index (AddMonoidHom.range (T : V →+ V))
    have hpos : 0 < Nat.card (AddMonoidHom.range (T : V →+ V)) := Nat.card_pos
    have : Nat.card (AddMonoidHom.range (T : V →+ V)) * (AddMonoidHom.range (T : V →+ V)).index
        = Nat.card (AddMonoidHom.range (T : V →+ V)) * K := by
      rw [b, ← a, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have step : ∀ k : ℕ, Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))
      ≤ K * Nat.card (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V)) := by
    intro k
    have h := card_le_card_ker_mul_card_map (T : V →+ V) (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))
    have e : (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)).map (T : V →+ V)
        = AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V) := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        refine ⟨x, ?_⟩
        rw [pow_succ']
        rfl
      · rintro ⟨x, rfl⟩
        refine ⟨(T ^ k) x, ⟨x, rfl⟩, ?_⟩
        rw [pow_succ']
        rfl
    rw [e] at h
    exact h
  have main : ∀ k : ℕ, Nat.card V
      ≤ K ^ k * Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Nat.one_mul]
      refine Nat.card_le_card_of_injective
        (fun x => (⟨x, x, by rw [pow_zero]; rfl⟩ :
          AddMonoidHom.range ((T ^ 0 : AddMonoid.End V) : V →+ V))) ?_
      intro a b hab
      simpa using congrArg Subtype.val hab
    | succ k ih =>
      calc Nat.card V
          ≤ K ^ k * Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)) := ih
        _ ≤ K ^ k * (K * Nat.card
            (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V))) :=
          Nat.mul_le_mul_left _ (step k)
        _ = K ^ (k + 1) * Nat.card
            (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V)) := by ring
  have hN1 : Nat.card (AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V)) ≤ 1 := by
    have hinj : Function.Injective
        (fun _ : AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V) => ()) := by
      rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ _
      apply Subtype.ext
      show (T ^ N) x = (T ^ N) y
      rw [hN]
      rfl
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  rw [hidx]
  calc Nat.card V
      ≤ K ^ N * Nat.card (AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V)) := main N
    _ ≤ K ^ N * 1 := Nat.mul_le_mul_left _ hN1
    _ = K ^ N := Nat.mul_one _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Nzd
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.nzd :
    ∀ (k A : Type) [CommRing k] [AddCommGroup A] (a : A) (x : AddMonoidAlgebra k A), (∀ m : ℕ, m • a = 0 → m = 0) → (1 - AddMonoidAlgebra.single a 1) * x = 0 → x = 0 := by
  intro k A _ _ a x ha h
  have hx : AddMonoidAlgebra.single a (1:k) * x = x := by
    rw [sub_mul, one_mul, sub_eq_zero] at h; exact h.symm
  have step : ∀ c, x.coeff (c + a) = x.coeff c := by
    intro c
    conv_lhs => rw [← hx]
    rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, add_comm c a, neg_add_cancel_left]
  have key : ∀ b (n : ℕ), x.coeff (b + n • a) = x.coeff b := by
    intro b n
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, ← add_assoc, step, ih]
  by_contra hne
  obtain ⟨b, hb⟩ : ∃ b, x.coeff b ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (AddMonoidAlgebra.ext (Finsupp.ext fun c => by simp [hc c]))
  have hinj : Function.Injective fun n : ℕ => b + n • a := by
    intro n m hnm
    simp only [add_right_inj] at hnm
    rcases le_total n m with hle | hle
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, left_eq_add] at hnm
      simp [ha d hnm]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, add_eq_left] at hnm
      simp [ha d hnm]
  exact Set.infinite_of_injective_forall_mem hinj
    (fun n => show b + n • a ∈ (x.coeff.support : Set A) by simp [key, hb])
    x.coeff.support.finite_toSet
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.POddRelIndexLe
section
open UpperTheory.V.FW

private theorem pOdd_relIndex_le (l : ℕ) (C : Type) [CommGroup C] [Finite C] (B : Subgroup C) :
    (powR (C := C) l).relIndex B ≤ Nat.card (B ⊓ torK (C := C) l : Subgroup C) := by
  have h1 : powR (C := B) l ≤ (powR (C := C) l).subgroupOf B := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(y : C), by simp⟩
  have h2 : ((powR (C := C) l).subgroupOf B).index ≤ (powR (C := B) l).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le h1)
  have h3 : (powR (C := B) l).index = Nat.card (torK (C := B) l) := by
    have a := Subgroup.index_mul_card (powR (C := B) l)
    have b := Subgroup.index_mul_card (torK (C := B) l)
    have c : (torK (C := B) l).index = Nat.card (powR (C := B) l) := Subgroup.index_ker _
    have d : 0 < Nat.card (powR (C := B) l) := Nat.card_pos
    rw [c, ← a, mul_comm] at b
    exact (Nat.eq_of_mul_eq_mul_right d b).symm
  have h4 : Nat.card (torK (C := B) l) ≤ Nat.card (B ⊓ torK (C := C) l : Subgroup C) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : C), x.1.2, ?_⟩ : (B ⊓ torK (C := C) l : Subgroup C))) ?_
    · have hx : x.1 ^ l = 1 := x.2
      show (x.1 : C) ^ l = 1
      rw [← Subgroup.coe_pow, hx]; rfl
    · intro x y hxy
      have e := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext e)
  exact h2.trans (h3.le.trans h4)

theorem UpperTheory.V.FW.pOdd :
    ∀ (l : ℕ) (C : Type) [CommGroup C] [Finite C] (J : C →* C), Odd l → (powR (C := C) l ⊔ difR J).index ≤ l * Nat.card (minK J ⊓ torK (C := C) l : Subgroup C) → (powR (C := C) l).index ≤ l * Nat.card (difR J ⊓ torK (C := C) l : Subgroup C) ^ 2 := by
  intro l C _ _ J hl h
  obtain ⟨k, hk⟩ := hl
  have h1 : minK J ⊓ torK (C := C) l ≤ difR J ⊓ torK (C := C) l := by
    rintro x ⟨hx, hx'⟩
    refine ⟨⟨x ^ (k + 1), ?_⟩, hx'⟩
    have a : J x * x = 1 := hx
    have b : x ^ l = 1 := hx'
    have c : J x = x⁻¹ := eq_inv_of_mul_eq_one_left a
    show x ^ (k + 1) / J (x ^ (k + 1)) = x
    rw [map_pow, c, inv_pow, div_inv_eq_mul, ← pow_add,
      show k + 1 + (k + 1) = l + 1 by omega, pow_succ, b, one_mul]
  have h2 : Nat.card (minK J ⊓ torK (C := C) l : Subgroup C) ≤ Nat.card (difR J ⊓ torK (C := C) l : Subgroup C) :=
    Subgroup.card_le_of_le h1
  have h3 := Subgroup.relIndex_mul_index (le_sup_left : powR (C := C) l ≤ powR (C := C) l ⊔ difR J)
  rw [Subgroup.relIndex_sup_left] at h3
  have h4 := pOdd_relIndex_le l C (difR J)
  calc (powR (C := C) l).index = (powR (C := C) l).relIndex (difR J) * (powR (C := C) l ⊔ difR J).index := h3.symm
    _ ≤ Nat.card (difR J ⊓ torK (C := C) l : Subgroup C) * (l * Nat.card (difR J ⊓ torK (C := C) l : Subgroup C)) :=
      Nat.mul_le_mul h4 (h.trans (Nat.mul_le_mul_left _ h2))
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PTwo
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.pTwo :
    ∀ (C : Type) [CommGroup C] [Finite C] (J : C →* C), (∀ x, J (J x) = x) →
      (powR (C := C) 2).index ≤
        ((difR J).relIndex (minK J) * Nat.card (difR J ⊓ torK (C := C) 2 : Subgroup C)) ^ 2 := by
  intro C _ _ J hJ
  classical
  have hcard : ∀ {G H : Type} [Group G] [Group H] (f : G →* H),
      Nat.card G = Nat.card f.ker * Nat.card f.range := by
    intro G H _ _ f
    rw [← f.ker.card_mul_index, Subgroup.index_ker]
  set T := torK (C := C) 2 with hT
  set D := difR J with hD
  set K := minK J with hK
  have memT : ∀ x : C, x ∈ T ↔ x ^ 2 = 1 := fun x => by simp [hT, torK]
  have memK : ∀ x : C, x ∈ K ↔ J x * x = 1 := fun x => by simp [hK, minK]
  have memD : ∀ x : C, x ∈ D ↔ ∃ y, y / J y = x := fun x => by simp [hD, difR]
  have hDK : D ≤ K := by
    intro x hx
    obtain ⟨y, rfl⟩ := (memD x).1 hx
    rw [memK, map_div, hJ, div_mul_div_comm, mul_comm (J y) y, div_self']
  have h1 : (powR (C := C) 2).index = Nat.card T := by
    have e1 := hcard (powMonoidHom 2 : C →* C)
    have e2 := (powR (C := C) 2).card_mul_index
    have hpos : 0 < Nat.card (powR (C := C) 2) := Nat.card_pos
    have e3 : Nat.card (powR (C := C) 2) * (powR (C := C) 2).index =
        Nat.card (powR (C := C) 2) * Nat.card T := by
      rw [e2, mul_comm]
      exact e1
    exact Nat.eq_of_mul_eq_mul_left hpos e3
  let g : T →* C := (MonoidHom.id C / J).comp T.subtype
  have e4 := hcard g
  have r1 : Nat.card g.range ≤ Nat.card (D ⊓ T : Subgroup C) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨t, rfl⟩
    have gt : g t = t.1 / J t.1 := rfl
    rw [gt, Subgroup.mem_inf]
    refine ⟨(memD _).2 ⟨t.1, rfl⟩, ?_⟩
    rw [memT, div_pow, ← map_pow, (memT _).1 t.2, map_one, div_one]
  have r2 : Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := by
    have hm : ∀ x : g.ker, (x.1.1 : C) ∈ K ⊓ T := by
      intro x
      have hx : g x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hT' : x.1.1 ^ 2 = 1 := (memT _).1 x.1.2
      have hd : x.1.1 / J x.1.1 = 1 := hx
      have hJx : J x.1.1 = x.1.1 := (div_eq_one.1 hd).symm
      refine Subgroup.mem_inf.2 ⟨(memK _).2 ?_, x.1.2⟩
      rw [hJx, ← pow_two, hT']
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (K ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  let incl : (K ⊓ T : Subgroup C) →* K := Subgroup.inclusion inf_le_left
  let h : (K ⊓ T : Subgroup C) →* K ⧸ D.subgroupOf K := (QuotientGroup.mk' (D.subgroupOf K)).comp incl
  have e5 := hcard h
  have r3 : Nat.card h.range ≤ D.relIndex K :=
    le_of_le_of_eq (Subgroup.card_le_card_group _) rfl
  have r4 : Nat.card h.ker ≤ Nat.card (D ⊓ T : Subgroup C) := by
    have hm : ∀ x : h.ker, (x.1.1 : C) ∈ D ⊓ T := by
      intro x
      have hx : h x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hx2 : incl x.1 ∈ D.subgroupOf K := (QuotientGroup.eq_one_iff _).1 hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hx2, (Subgroup.mem_inf.1 x.1.2).2⟩
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (D ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  rw [h1]
  set r := D.relIndex K
  set d := Nat.card (D ⊓ T : Subgroup C)
  have s1 : Nat.card T ≤ (r * d) * d := by
    rw [e4]
    apply Nat.mul_le_mul _ r1
    calc Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := r2
      _ = Nat.card h.ker * Nat.card h.range := e5
      _ ≤ d * r := Nat.mul_le_mul r4 r3
      _ = r * d := mul_comm _ _
  have s2 : (r * d) * d ≤ (r * d) ^ 2 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · simp [hr]
    · rw [pow_two]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left d hr)
  exact s1.trans s2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PushDiff
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.pushDiff :
    ∀ (k : Type) [CommRing k] (M m : ℕ) [NeZero M] (h : m ∣ M) (N : ℕ) (P : ℕ → k) (g : ZMod M → k), (∀ s, g s - g (s - N) = ∑ j ∈ Finset.range N, if (j : ZMod M) = s then P j else 0) → ∀ y : ZMod m, push h g y - push h g (y - N) = ∑ j ∈ Finset.range N, if (j : ZMod m) = y then P j else 0 := by
  intro k _ M m _ h N P g hg y
  simp only [push]
  have shift : (∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y - N), g s)
      = ∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y), g (s - N) := by
    apply Finset.sum_nbij' (fun s : ZMod M => s + (N : ZMod M)) (fun s : ZMod M => s - (N : ZMod M))
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_add (f := _), hs, map_natCast]
      ring
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_sub, hs, map_natCast]
    · intro s _
      ring
    · intro s _
      ring
    · intro s _
      congr 1
      ring
  rw [shift, ← Finset.sum_sub_distrib]
  simp_rw [hg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_ite_eq]
  have key : (j : ZMod M) ∈ Finset.univ.filter
      (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y) ↔ (j : ZMod m) = y := by
    rw [Finset.mem_filter, ZMod.castHom_apply, ZMod.cast_natCast h]
    simp
  by_cases hj : (j : ZMod m) = y
  · rw [if_pos (key.mpr hj), if_pos hj]
  · rw [if_neg (fun t => hj (key.mp t)), if_neg hj]
end

