module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0019
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgLimit
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_limit :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsVertexRing C 𝔪 → IsModel O C 𝔪 ρ → ∃ (ξ : S.A →ₐ[O] D) (β : S.B →ₐ[O] C), S.u.map (ξ : S.A →+* D) = ρ ∧ ∀ b, ξ (S.inc b) = algebraMap C D (β b) := by
  intro l _ O _ _ F n S C _ _ _ D _ _ _ _ 𝔪 ρ hV hM
  obtain ⟨f, hf1, hf2, hf3⟩ := alg_family S C 𝔪 ρ hV hM
  haveI : IsAdicComplete (maximalIdeal C) C := IsCO.complete (O := O)
  have hsep : ∀ d d' : D, (∀ N : ℕ, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = Ideal.Quotient.mk (𝔪 ^ (N + 1)) d') → d = d' := by
    intro d d' h
    have hmem : d - d' ∈ ⨅ N, 𝔪 ^ N := by
      refine (Submodule.mem_iInf _).2 fun N => ?_
      cases N with
      | zero => simp
      | succ N => exact Ideal.Quotient.eq.1 (h N)
    rw [hV.sep] at hmem
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hmem)
  have hr : ∀ N g i j, f N (S.ρ.r g i j) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ρ.r g i j) := by
    intro N g i j
    have := congrArg (fun σ => σ.r g i j) (hf1 N)
    simpa only [NRep.map_r, AlgHom.coe_toRingHom] using this
  have hψ : ∀ N v i g, f N ((S.ρ.ψ v i g : S.R)) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ρ.ψ v i g : D) := by
    intro N v i g
    have := congrArg (fun σ => ((σ.ψ v i g : Units _) : D ⧸ 𝔪 ^ (N + 1))) (hf1 N)
    simpa only [NRep.map_ψ, AlgHom.coe_toRingHom] using this
  let T' : Subalgebra O S.R :=
    { carrier := {x | ∃ c : C, ∀ N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D c) = f N x}
      mul_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c * c', fun N => by simp only [map_mul, hc, hc']⟩
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c + c', fun N => by simp only [map_add (f := _), hc, hc']⟩
      algebraMap_mem' := fun a => ⟨algebraMap O C a, fun N => by
        rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
        rfl⟩ }
  let T : Subalgebra O S.R :=
    { carrier := {x | ∃ d : D, ∀ N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N x}
      mul_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c * c', fun N => by simp only [map_mul, hc, hc']⟩
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c + c', fun N => by simp only [map_add (f := _), hc, hc']⟩
      algebraMap_mem' := fun a => ⟨algebraMap O D a, fun N => by
        rw [AlgHom.commutes]
        rfl⟩ }
  have hgen : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ↑((S.ρ.ψ v i) g)}) ≤ T' := by
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨v, i, g, rfl⟩)
    · obtain ⟨L, hL, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hM.mon _ ⟨L, hL, rfl⟩
      refine ⟨c, fun N => ?_⟩
      rw [hc, map_list_prod, map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left ?_
      intro s _
      simp only [Function.comp, hr]
    · obtain ⟨c, hc, -⟩ := hM.psi v i g
      exact ⟨c, fun N => by rw [hc, hψ]⟩
  have hB : S.B ≤ T' := by
    intro x hx
    have hx' : ∀ N : ℕ, ∃ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ↑((S.ρ.ψ v i) g)}), x - y ∈ maximalIdeal S.R ^ N := hx
    choose y hy hxy using hx'
    choose c hc using fun N => hgen (hy (N + 1))
    have hfx : ∀ N M, N + 1 ≤ M → f N x = f N (y M) := by
      intro N M hNM
      have h0 := hf3 N _ (Ideal.pow_le_pow_right hNM (hxy M))
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have hcau : ∀ N : ℕ, algebraMap C D (c (N + 1) - c N) ∈ 𝔪 ^ (N + 1) := by
      intro N
      rw [map_sub]
      refine Ideal.Quotient.eq.1 ?_
      rw [hc, hc, ← hfx N (N + 1 + 1) (by omega), ← hfx N (N + 1) le_rfl]
    obtain ⟨z, hz⟩ := alg_closed C 𝔪 hV c hcau
    refine ⟨z, fun N => ?_⟩
    have h1 : Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D z) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D (c N)) := by
      refine Ideal.Quotient.eq.2 ?_
      rw [← map_sub]
      exact hz N
    rw [h1, hc, ← hfx N (N + 1) le_rfl]
  have hA : S.A ≤ T := by
    show Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) ≤ T
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · obtain ⟨c, hc⟩ := hB hx
      exact ⟨algebraMap C D c, hc⟩
    · exact ⟨ρ.r g i j, fun N => (hr N g i j).symm⟩
  obtain ⟨ξ, hξ⟩ := alg_glue (A := S.A) 𝔪 hV.sep (fun N => (f N).comp S.A.val) (fun a => by
    obtain ⟨d, hd⟩ := hA a.2
    exact ⟨d, fun N => by simpa using hd N⟩)
  have hξ' : ∀ (a : S.A) N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ξ a) = f N (a : S.R) := by
    intro a N
    simpa using hξ a N
  let φ := IsScalarTower.toAlgHom O C D
  have hmem : ∀ b, (ξ.comp S.inc) b ∈ φ.range := by
    intro b
    obtain ⟨c, hc⟩ := hB b.2
    refine (AlgHom.mem_range φ).2 ⟨c, ?_⟩
    refine hsep _ _ fun N => ?_
    show Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D c) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ξ (S.inc b))
    rw [hc, hξ']
    rfl
  let e := AlgEquiv.ofInjective φ hV.inj
  refine ⟨ξ, e.symm.toAlgHom.comp ((ξ.comp S.inc).codRestrict φ.range hmem), ?_, ?_⟩
  · refine NRep.ext ?_ ?_
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      rw [NRep.map_r]
      refine hsep _ _ fun N => ?_
      rw [← hr]
      exact hξ' _ N
    · funext v i
      refine MonoidHom.ext fun g => Units.ext ?_
      rw [NRep.map_ψ]
      refine hsep _ _ fun N => ?_
      rw [← hψ]
      exact hξ' _ N
  · intro b
    have h1 : ((e (e.symm ⟨ξ (S.inc b), hmem b⟩) : φ.range) : D) = φ (e.symm ⟨ξ (S.inc b), hmem b⟩) :=
      AlgEquiv.ofInjective_apply _ _ _
    rw [AlgEquiv.apply_symm_apply] at h1
    exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.co_B :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∃ h : IsCO O S.B, @maximalIdeal _ _ h.toIsLocalRing = S.mB := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, -, hB, -, -⟩ := UpperTheory.V.Fr.wpres hF hn S
  haveI h0 : IsCO O (W.gr 0) := UpperTheory.V.Alg.wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ S.R W hz
  let p : W.gr 0 →ₐ[O] S.B :=
    { toFun := fun b => ⟨((b : W.A) : S.R), (hB _).2 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hp : Function.Surjective p := fun y =>
    ⟨⟨⟨y.1, W.part_le_A ((hB _).1 y.2)⟩, (hB _).1 y.2⟩, rfl⟩
  haveI h : IsCO O S.B := UpperTheory.V.Alg.co_quot O (W.gr 0) S.B p hp
  refine ⟨h, ?_⟩
  ext b
  show _ ↔ S.B.val b ∈ maximalIdeal S.R
  rw [← res_eq_zero_iff O, ← res_eq_zero_iff O, res_map]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGco
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_gco :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] (p : C' →ₐ[O] C) (σ' : C' →ₐ[O] C') (B : Box F 3 C) (π : F.V → Fin 3 → ZMod 2) (D : SetLift p B), D.Gr σ' π → ∀ j, ∀ u ∈ formp σ' (RingHom.ker p) j, (∀ x, (D.co u).1 x ∈ adp (ResidueField O) j) ∧ ∀ v s, (D.co u).2 v s ∈ adp (ResidueField O) j := by
  intro l _ k _ F O _ _ C' _ _ _ C _ _ p σ' B π D hD j u hu
  have hu' : ∀ i, i ≠ j → ∀ y : RingHom.ker p, (y : C') ∈ evp σ' i → u y = 0 := hu
  have key : ∀ M : Matrix (Fin 3) (Fin 3) C', GrM σ' pq pq M →
      M.map (evK (RingHom.ker p) u) ∈ adp (ResidueField O) j := by
    intro M hM
    change ∀ a b, pw a b ≠ j → M.map (evK (RingHom.ker p) u) a b = 0
    intro a b hab
    rw [Matrix.map_apply]
    have hmem := hM a b
    rw [← pw_eq] at hmem
    unfold evK
    split_ifs with hk
    · exact hu' (pw a b) hab ⟨M a b, hk⟩ hmem
    · rfl
  obtain ⟨h1, hsub, hmul, hinv, hsgn⟩ := ep_grm σ'
  refine ⟨fun x => ?_, fun v s => ?_⟩
  · refine key (D.om x) ?_
    unfold SetLift.om
    rw [Units.val_mul, Units.val_mul]
    exact hsub _ _ _ _ (hmul _ _ _ _ _ (hmul _ _ _ _ _ (hD.r x.1) (hsgn _ _ (hD.r x.2)))
      (hinv _ _ _ (hD.r (x.1 * x.2)))) (h1 pq)
  · have hX : GrM σ' pq pq ↑((D.g v)⁻¹ * D.t v s * D.g v) := by
      rw [Units.val_mul, Units.val_mul]
      exact hmul _ _ _ _ _ (hmul _ _ _ _ _ (hinv _ _ _ (hD.g v)) (hD.t v s)) (hD.g v)
    refine key (D.a v s) ?_
    unfold SetLift.a
    rw [Units.val_mul]
    exact hsub _ _ _ _ (hmul _ _ _ _ _ (hD.r _) (hinv _ _ _ hX)) (h1 pq)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGflag
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_mul_self (R : Type) [CommRing R] (j : ZMod 2) : sg R j * sg R j = 1 := by
  rw [sg, ← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem sg_sub (R : Type) [CommRing R] (i j : ZMod 2) : sg R (i - j) = sg R i * sg R j := by
  have key : ∀ a b : ZMod 2, (a - b).val % 2 = (a.val + b.val) % 2 := by decide
  rw [sg, sg, sg, ← pow_add, neg_one_pow_eq_pow_mod_two, key, ← neg_one_pow_eq_pow_mod_two]

private theorem map_sg {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) :
    σ (sg R j) = sg R j := by simp [sg]

private theorem grM_iff {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ σ.mapMatrix M = diagonal (fun a => sg R (α a)) * M * diagonal (fun b => sg R (β b)) := by
  unfold GrM
  rw [← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  change σ (M a b) = sg R (α a - β b) * M a b ↔ _
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, sg_sub]
  constructor <;> intro h <;> rw [h] <;> ring

private theorem diag_sq (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) :
    diagonal (fun a => sg R (α a)) * diagonal (fun a => sg R (α a)) = 1 := by
  rw [diagonal_mul_diagonal]
  simp only [sg_mul_self]
  exact diagonal_one

private theorem map_diag {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α : Fin 3 → ZMod 2) :
    σ.mapMatrix (diagonal (fun a => sg R (α a))) = diagonal (fun a => sg R (α a)) := by
  rw [AlgHom.mapMatrix_apply, Matrix.diagonal_map (map_zero σ)]
  simp only [map_sg]

private theorem exists_sign {R : Type} [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) (x : R) :
    ∃ j : ZMod 2, IsUnit (1 + sg R j * x) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := 1 + x) (b := 1 - x)
      (by convert h2 using 1; ring) with h | h
  · refine ⟨0, ?_⟩
    simpa [sg] using h
  · refine ⟨1, ?_⟩
    rw [show sg R 1 = -1 from by rw [sg, show (1 : ZMod 2).val = 1 from rfl, pow_one]]
    simpa [sub_eq_add_neg] using h

theorem UpperTheory.V.Fr.ep_gflag :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ {H : Type} (r : H → Matrix (Fin 3) (Fin 3) R) (g : GL (Fin 3) R), (∀ s, GrM σ pq pq (r s)) → (∀ s, UpT ((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R))) → (∀ s i, ((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i i ∈ evp σ 0) → (∃ s, ∀ i j, i ≠ j → IsUnit (((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i i - ((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) j j)) → ∃ (u : GL (Fin 3) R) (α : Fin 3 → ZMod 2), UpT (u : Matrix (Fin 3) (Fin 3) R) ∧ GrM σ α pq ((u * g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  intro O _ _ _ _ h2 R _ _ _ σ hσ H r g hr hT hd hs
  have h2R : IsUnit (2 : R) := by
    have := h2.map (algebraMap O R)
    rwa [map_ofNat] at this
  obtain ⟨s0, hs0⟩ := hs
  have hT0 := hT s0
  have hd0 := hd s0
  set G : Matrix (Fin 3) (Fin 3) R := (g : Matrix (Fin 3) (Fin 3) R) with hGdef
  set Gi : Matrix (Fin 3) (Fin 3) R := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) with hGidef
  have hGGi : G * Gi = 1 := g.mul_inv
  have hGiG : Gi * G = 1 := g.inv_mul
  set P : Matrix (Fin 3) (Fin 3) R := diagonal (fun a => sg R (pq a)) with hPdef
  have hPP : P * P = 1 := diag_sq R pq
  have hσP : σ.mapMatrix P = P := map_diag σ pq
  have hSS : ∀ M : Matrix (Fin 3) (Fin 3) R, σ.mapMatrix (σ.mapMatrix M) = M := by
    intro M
    ext i j
    simp [AlgHom.mapMatrix_apply, hσ]
  have hσr : σ.mapMatrix (r s0) = P * r s0 * P := (grM_iff σ pq pq (r s0)).1 (hr s0)
  have hσGiG : σ.mapMatrix Gi * σ.mapMatrix G = 1 := by rw [← map_mul, hGiG, map_one]
  obtain ⟨h, hh⟩ : ∃ h, h = G * P * σ.mapMatrix Gi := ⟨_, rfl⟩
  have hσh : σ.mapMatrix h = σ.mapMatrix G * P * Gi := by
    rw [hh, map_mul, map_mul, hσP, hSS]
  have hhσh : h * σ.mapMatrix h = 1 := by
    rw [hσh, hh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (σ.mapMatrix Gi), hσGiG, Matrix.one_mul, ← Matrix.mul_assoc P P, hPP,
      Matrix.one_mul, hGGi]
  have hUh : UpT h := by
    set T := G * r s0 * Gi with hTdef
    refine ep_upt h (σ.mapMatrix T) T ?_ hT0 ?_ ?_
    · intro i j hij
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, hT0 i j hij, map_zero]
    · intro i j hij
      have hfix : σ (T j j) = T j j := by
        have := hd0 j
        change σ (T j j) = sg R 0 * T j j at this
        rw [this, sg, ZMod.val_zero, pow_zero, one_mul]
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, hfix]
      exact hs0 j i hij.ne
    · rw [hh, hTdef, map_mul, map_mul, hσr]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (σ.mapMatrix Gi) (σ.mapMatrix G), hσGiG, Matrix.one_mul,
        ← Matrix.mul_assoc P P, hPP, Matrix.one_mul, ← Matrix.mul_assoc Gi G, hGiG, Matrix.one_mul]
  have hex : ∀ i, ∃ j : ZMod 2, IsUnit (1 + sg R j * h i i) := fun i => exists_sign h2R (h i i)
  choose α hα using hex
  set D : Matrix (Fin 3) (Fin 3) R := diagonal (fun a => sg R (α a)) with hDdef
  have hDD : D * D = 1 := diag_sq R α
  have hσD : σ.mapMatrix D = D := map_diag σ α
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 1 + h * D := ⟨_, rfl⟩
  have hYU : Y.BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    rw [hY, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij'), hDdef, Matrix.mul_diagonal,
      hUh i j hij', zero_mul, add_zero]
  have hYdet : IsUnit Y.det := by
    rw [Matrix.det_of_upperTriangular hYU, Fin.prod_univ_three]
    have hu : ∀ i, IsUnit (Y i i) := by
      intro i
      rw [hY, Matrix.add_apply, Matrix.one_apply_eq, hDdef, Matrix.mul_diagonal, mul_comm]
      exact hα i
    exact ((hu 0).mul (hu 1)).mul (hu 2)
  have hYu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).2 hYdet
  set Yi : Matrix (Fin 3) (Fin 3) R := ((hYu.unit⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
    with hYidef
  have hYYi : Y * Yi = 1 := hYu.mul_val_inv
  have hYiY : Yi * Y = 1 := hYu.val_inv_mul
  have hUYi : UpT Yi := by
    haveI : Invertible Y := ⟨Yi, hYiY, hYYi⟩
    have := Matrix.blockTriangular_inv_of_blockTriangular hYU
    rw [Matrix.inv_eq_left_inv hYiY] at this
    exact fun i j hij => this hij
  have hσYσYi : σ.mapMatrix Y * σ.mapMatrix Yi = 1 := by rw [← map_mul, hYYi, map_one]
  have hYeq : h * σ.mapMatrix Y = Y * D := by
    rw [hY, map_add (f := _), map_one, map_mul, hσD, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
      Matrix.one_mul, ← Matrix.mul_assoc, hhσh, Matrix.one_mul, Matrix.mul_assoc, hDD,
      Matrix.mul_one, add_comm]
  have hGP : h * σ.mapMatrix G = G * P := by
    rw [hh, Matrix.mul_assoc, hσGiG, Matrix.mul_one]
  have hYih : Yi * h = D * σ.mapMatrix Yi := by
    calc Yi * h = Yi * (h * (σ.mapMatrix Y * σ.mapMatrix Yi)) := by rw [hσYσYi, Matrix.mul_one]
      _ = Yi * (Y * D) * σ.mapMatrix Yi := by rw [← hYeq]; simp only [Matrix.mul_assoc]
      _ = D * σ.mapMatrix Yi := by rw [← Matrix.mul_assoc Yi Y, hYiY, Matrix.one_mul]
  refine ⟨hYu.unit⁻¹, α, hUYi, ?_⟩
  rw [grM_iff, Units.val_mul]
  change σ.mapMatrix (Yi * G) = D * (Yi * G) * P
  rw [map_mul, Matrix.mul_assoc D, Matrix.mul_assoc Yi, ← hGP, ← Matrix.mul_assoc Yi, hYih,
    Matrix.mul_assoc D, ← Matrix.mul_assoc D D, hDD, Matrix.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsLocallyConstantTwistedCocycleNeZeroOfFrameOk
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_open_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

theorem UpperTheory.exists_locallyConstant_twistedCocycle_ne_zero_of_frameOk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ u : F.G0 → k, IsLocallyConstant u ∧ (∀ g h : F.G0, u (g * h) = (F.Ψ h : k) * u g + u h) ∧ (∀ g : F.G0, u (F.star g) = (((F.Ψ g)⁻¹ : kˣ) : k) * u g) ∧ (∀ v, ∃ α : k, ∀ s, u (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) * α) ∧ u ≠ 0 := by
  intro l _ k _ _ F C₀ h
  have hχ : ∀ g : F.G0, (F.Ψ⁻¹ * F.delK k) (g : F.Γ) = (F.Ψ g)⁻¹ := fun g => by
    have hg : F.del (g : F.Γ) = 1 := g.2
    simp [Frame.delK, hg]
  have hc : (F.Ψ⁻¹ * F.delK k) F.c = -1 := by
    apply Units.ext
    simp [Frame.delK, h.Ψ_c, h.del_c]
  have hl : ∀ v s, F.loc v s = ((F.loc0 v s : F.G0) : F.Γ) := fun _ _ => rfl
  obtain ⟨x, x1, x2, x3, x4, g₁, x5⟩ := UpperTheory.smooth_vector_fixed_by_open_subgroup h (F.Ψ⁻¹ * F.delK k) hc (fun v => by
    obtain ⟨s, hs⟩ := h.f3 v
    refine ⟨s, fun e => hs ?_⟩
    rw [hl, hχ, inv_eq_one] at e
    rw [hl, e, one_pow]) h.f4
  have x0 : x 1 = 0 := by
    have := x2 1 1
    simpa using this
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  refine ⟨fun g => x g * (F.Ψ g : k), ?_, fun g g' => ?_, fun g => ?_, fun v => ?_, fun e => x5 ?_⟩
  · exact (x1.mul ((lc_of_open_ker F.Ψ h.Ψ_open).comp Units.val)).comp_continuous continuous_subtype_val
  · show x ((g : F.Γ) * g') * (F.Ψ ((g : F.Γ) * g') : k) = _
    rw [x2, hχ, map_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    have := (F.Ψ g).ne_zero
    field_simp
  · have hs : ((F.star g : F.G0) : F.Γ) = F.c * ((g : F.Γ)⁻¹ * F.c) := by
      show F.c * (g : F.Γ)⁻¹ * F.c⁻¹ = _
      rw [hci, mul_assoc]
    have h1 : x (g : F.Γ)⁻¹ + (F.Ψ g : k) * x g = 0 := by
      have := x2 (g : F.Γ)⁻¹ g
      rw [inv_mul_cancel, x0, map_inv, hχ, inv_inv] at this
      exact this.symm
    have hΨstar : F.Ψ (F.star g) = (F.Ψ g)⁻¹ := by
      have : ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm]
    show x (F.star g) * (F.Ψ (F.star g) : k) = _
    rw [hΨstar, hs, x2, x2, x3, hc]
    simp only [Units.val_neg, Units.val_one]
    linear_combination (-(((F.Ψ g)⁻¹ : kˣ) : k)) * h1
  · obtain ⟨Y, hY⟩ := x4 v
    refine ⟨-Y, fun s => ?_⟩
    show x (F.loc v s) * (F.Ψ (F.loc v s) : k) = _
    rw [hY, hl, hχ, Units.val_inv_eq_inv_val]
    have := (F.Ψ (F.loc0 v s)).ne_zero
    field_simp
    ring
  · exact (mul_eq_zero.1 (congrFun e g₁)).resolve_right (F.Ψ g₁).ne_zero
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsMemStrSNeZeroOfFrameOk
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] (f : G →* H)
    (hf : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf

theorem UpperTheory.exists_mem_strS_ne_zero_of_frameOk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ b ∈ F.strS k, b ≠ 0 := by
  intro l _ k _ _ F C₀ h
  have hχ0 : ∀ g : F.G0, (F.Ψ⁻¹ ^ 2 * F.delK k) g = (F.Ψ g)⁻¹ ^ 2 := fun g => by
    have : F.del g = 1 := g.2
    simp [Frame.delK, this]
  have hχ : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k))⁻¹ ^ 2 := fun g => by
    rw [hχ0]; simp
  have hc : (F.Ψ⁻¹ ^ 2 * F.delK k) F.c = -1 := by
    apply Units.ext
    simp [Frame.delK, h.Ψ_c, h.del_c]
  obtain ⟨x, x1, x2, x3, x4, g₁, x5⟩ := UpperTheory.smooth_vector_fixed_by_open_subgroup h (F.Ψ⁻¹ ^ 2 * F.delK k) hc (fun v => by
    obtain ⟨s, hs⟩ := h.f3 v
    refine ⟨s, fun e => hs ?_⟩
    have e' := (hχ0 (F.loc0 v s)).symm.trans e
    rw [inv_pow, inv_eq_one] at e'
    exact e') h.f4'
  have x0 : x 1 = 0 := by
    have := x2 1 1
    rw [mul_one, map_one] at this
    simpa using this
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  refine ⟨fun g => x g * F.Ψ g, ⟨?_, fun g g' => ?_, fun g => ?_, fun v => ?_⟩, fun e => ?_⟩
  · exact (x1.mul ((lc_of_ker F.Ψ h.Ψ_open).comp Units.val)).comp_continuous continuous_subtype_val
  · have := (F.Ψ g).ne_zero
    simp only [Subgroup.coe_mul, x2, hχ, map_mul, Units.val_mul, smul_eq_mul, Units.val_inv_eq_inv_val]
    field_simp
  · have hs : ((F.star g : F.G0) : F.Γ) = F.c * ((g : F.Γ)⁻¹ * F.c) := by
      rw [← mul_assoc]
      nth_rewrite 2 [← hci]
      rfl
    have h0 := (F.Ψ g).ne_zero
    have e1 := x2 g (g : F.Γ)⁻¹
    rw [mul_inv_cancel, x0, hχ] at e1
    show x (F.star g) * F.Ψ (F.star g) = x g * F.Ψ g
    have hstar : F.Ψ (F.star g) = (F.Ψ g)⁻¹ := by
      rw [hs, map_mul, map_mul, map_inv, h.Ψ_c]
      simp
    rw [hstar, hs, x2, x2, x3, hc, Units.val_inv_eq_inv_val]
    have e2 : x g = -((F.Ψ g : k)⁻¹ ^ 2 * x (g : F.Γ)⁻¹) := by linear_combination -e1
    rw [e2]
    simp only [Units.val_neg, Units.val_one]
    field_simp
    ring
  · obtain ⟨Y, hY⟩ := x4 v
    refine ⟨-Y, fun s => ?_⟩
    have h0 := (F.Ψ (F.loc v s)).ne_zero
    have e : (((F.Ψ⁻¹ ^ 2 * F.delK k) (F.loc v s) : kˣ) : k) = ((F.Ψ (F.loc v s) : k))⁻¹ ^ 2 := hχ (F.loc0 v s)
    show x (F.loc v s) * F.Ψ (F.loc v s) = _
    rw [hY, e, Units.val_inv_eq_inv_val, smul_eq_mul]
    field_simp
    ring
  · exact mul_ne_zero x5 (F.Ψ g₁).ne_zero (congrFun e g₁)
end

