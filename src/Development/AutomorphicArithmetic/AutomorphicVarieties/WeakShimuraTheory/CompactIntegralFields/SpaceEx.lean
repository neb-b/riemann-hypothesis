module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxUnivD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.GenZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0006

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.spaceEx :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → Nonempty (Space Φ a) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS
  haveI : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  obtain ⟨R, _, _, _, D, hU⟩ := sxUnivD l hS
  obtain ⟨W, hW⟩ := sxGradD hU
  haveI : IsCO Λ (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal Λ (ℤ × ℤ) R W hW.max
  haveI : IsScalarTower Λ (W.gr 0) W.A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨D', hD', hrep⟩ := sxSubRD a W.A D (fun g i j => W.part_le_A (hW.ent g i j))
    (fun v i s => W.part_le_A (hW.chr v i s)) hU.1.rep
  have hψ : ∀ v i s, (W.A.val (D'.ψ v i s) : R) = D.ψ v i s := by
    intro v i s
    rw [← hD']
    rfl
  have hr : ∀ g i j, (W.A.val (D'.r g i j) : R) = D.r g i j := by
    intro g i j
    rw [← hD']
    rfl
  have hcp : ∃ cp : Γ → (W.gr 0)[X],
      (∀ g, (cp g).map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly) ∧
      (∀ n, AdicCont (maximalIdeal (W.gr 0)) fun g => (cp g).coeff n) ∧
      ∀ g, (cp g).map (res Λ (W.gr 0) : W.gr 0 →+* ResidueField Λ) =
        ∏ i, (X - C (residue Λ (a (Φ.χ i g)))) := by
    have hr' : ∀ g, D.r g = (D'.r g).map (W.A.val : W.A →+* R) := fun g => by
      rw [← hD']; rfl
    have hent : ∀ g i j, D'.r g i j ∈ W.gr (wt i j) := fun g i j => by
      have h := hW.ent g i j
      rw [hr'] at h
      exact h
    have hc : ∀ g n, (D'.r g).charpoly.coeff n ∈ W.gr 0 :=
      fun g n => sxCpZero W.gr (D'.r g) (hent g) n
    have hl : ∀ g, ∃ p : (W.gr 0)[X], p.map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly := fun g => by
      have h : (D'.r g).charpoly ∈ Polynomial.lifts (algebraMap (W.gr 0) W.A) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨_, hc g n⟩, rfl⟩
      exact (Polynomial.mem_lifts _).1 h
    choose cp hcp using hl
    have hco : ∀ g n, (((cp g).coeff n : W.A) : R) = (D.r g).charpoly.coeff n := fun g n => by
      rw [hr', Matrix.charpoly_map, coeff_map, ← hcp, coeff_map]
      rfl
    refine ⟨cp, hcp, fun n => ?_, fun g => ?_⟩
    · refine (sxContGr W hW.max).2 _ ?_
      simp only [hco]
      exact (sxAdicMat (maximalIdeal R) (fun g => D.r g) hU.1.cont).1 n
    · let f : W.gr 0 →ₐ[Λ] R :=
        { (W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A) with
          commutes' := fun _ => rfl }
      have hd : (D.r g).map (res Λ R : R →+* ResidueField Λ) =
          Matrix.diagonal fun i => residue Λ (a (Φ.χ i g)) := by
        ext i j
        by_cases h : i = j
        · subst h
          rw [Matrix.diagonal_apply_eq]
          exact hU.1.diag g i
        · rw [Matrix.diagonal_apply_ne _ h]
          exact (res_eq_zero_iff Λ R _).2 (hU.1.off g i j h le_rfl)
      rw [← Matrix.charpoly_diagonal, ← hd, Matrix.charpoly_map]
      ext n
      rw [coeff_map, coeff_map, ← hco]
      exact (res_map f _).symm
  obtain ⟨cp, hcp1, hcp2, hcp3⟩ := hcp
  have sxCoreGen :
      ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) = ⊤ := by
    intro O Γ _ _ _ Φ Λ _ _ _ _ R _ _ _ D W hD D' hmap
    have hr : ∀ g i j, D.r g i j = (D'.r g i j : R) := by
      subst hmap
      intro g i j
      first | rfl | simp [RD.map]
    have hψ : ∀ v i t, D.ψ v i t = (D'.ψ v i t : R) := by
      subst hmap
      intro v i t
      first | rfl | simp [RD.map]
    set S := Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) with hS
    have hbA : ∀ b : W.gr 0, algebraMap (W.gr 0) W.A b = (b : W.A) := fun b => by first | rfl | simp
    have hgr : ∀ x : W.A, (x : R) ∈ W.part 0 → x ∈ S := by
      intro x hx
      have h := Subalgebra.algebraMap_mem S (⟨x, hx⟩ : W.gr 0)
      rwa [hbA] at h
    have hc : ∀ c : Λ, algebraMap Λ W.A c ∈ S := by
      intro c
      apply hgr
      have h0 : algebraMap Λ R c ∈ W.part 0 := by
        have := (algebraMap Λ (W.gr 0) c).2
        first
          | exact this
          | (have e : ((algebraMap Λ (W.gr 0) c : W.A) : R) = algebraMap Λ R c := by first | rfl | simp
             rw [← e]; exact this)
      first | exact h0 | simpa using h0
    have hr' : ∀ g i j, D'.r g i j ∈ S := fun g i j => Algebra.subset_adjoin ⟨(g, i, j), rfl⟩
    have hz : ∀ s, W.zA s ∈ S := by
      intro s
      rcases hD.var s with ⟨g, i, j, c, hzs, -, -⟩ | ⟨v, i, t, c, hzs, -⟩
      · have e : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
          apply Subtype.ext
          show W.z s = _
          rw [hzs, hr]
          rfl
        rw [e]
        exact sub_mem (hr' g i j) (hc c)
      · have e : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
          apply Subtype.ext
          show W.z s = _
          rw [hzs, hψ]
          rfl
        rw [e]
        refine sub_mem (hgr _ ?_) (hc c)
        rw [← hψ]
        exact hD.chr v i t
    rw [eq_top_iff]
    intro a ha0
    clear ha0
    have ha : a ∈ Algebra.adjoin Λ (↑(W.gr 0) ∪ Set.range W.zA) := by
      rw [gr_gen Λ R (ℤ × ℤ) W]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨s, rfl⟩
      · exact hgr x hx
      · exact hz s
    | algebraMap c => exact hc c
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete {R : Type} [CommRing R] [IsLocalRing R]
      [IsAdicComplete (maximalIdeal R) R] {x y : R}
      (h : ∀ N : ℕ, x - y ∈ maximalIdeal R ^ (N + 1)) : x = y := by
    rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)]
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    cases n with
    | zero => simp
    | succ N => exact h N

  have nontrivial_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ) :
      Nontrivial (R ⧸ maximalIdeal R ^ (N + 1)) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    intro h
    apply (maximalIdeal.isMaximal R).ne_top
    exact top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero N))

  have isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ)
      [IsLocalRing (R ⧸ maximalIdeal R ^ (N + 1))] :
      IsNilpotent (maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1))) := by
    refine ⟨N + 1, ?_⟩
    have hle : maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1)) ≤
        (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1))) := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply Ideal.mem_map_of_mem
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      exact fun hu => hx (hu.map _)
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    calc _ ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1)))) ^ (N + 1) :=
          Ideal.pow_right_mono hle _
      _ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have sxNearA :
      ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
    intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hQ
    classical
    have liftNilpotent : ∀ (T : Type) [CommRing T] [Algebra Λ T] [IsCO Λ T] (P : RD Φ T),
        IsNilpotent (maximalIdeal T) → Φ.Near a τ P → ∃ f : W.A →ₐ[Λ] T, D'.map (f : W.A →+* T) = P := by
      intro T _ _ _ P hnil hP
      let c := ∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs
      have hc : ∀ i j, -(c : ℤ) ≤ τ (wt i j) := by
        intro i j
        have h : (τ (wt i j)).natAbs ≤ c :=
          Finset.single_le_sum (f := fun p : Fin 4 × Fin 4 => (τ (wt p.1 p.2)).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
        omega
      obtain ⟨S, _, _, _, e, he⟩ := sxLaur (Λ := Λ) hnil c
      obtain ⟨P', hP', hr, hψ⟩ := sxScaleRD hnil he hc hP
      obtain ⟨F, hF, -⟩ := hU.2 S P' hP'
      have hFr : ∀ g i j, e (F (D.r g i j)) = HahnSeries.single (τ (wt i j)) (P.r g i j) := by
        intro g i j
        rw [← hr, ← hF]
        rfl
      have hFψ : ∀ v i s, e (F (D.ψ v i s)) = HahnSeries.single 0 (P.ψ v i s) := by
        intro v i s
        rw [← hψ, ← hF]
        rfl
      have hz : ∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y := by
        intro s
        rcases hG.var s with ⟨g, i, j, x, h1, h2, h3⟩ | ⟨v, i, t, x, h1, h2⟩
        · rw [h1, h2, map_sub, map_sub, hFr, AlgHom.commutes, he.alg]
          by_cases hij : i = j
          · rw [(wt_eq_zero i j).2 hij, map_zero]
            exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
          · rw [h3 hij]
            exact ⟨P.r g i j, by simp⟩
        · rw [h1, h2, map_sub, map_sub, hFψ, AlgHom.commutes, he.alg, map_zero]
          exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
      obtain ⟨f, hf⟩ := sxLaurDesc W he τ F (sxLaurPart W hG.max he τ F hz)
      have er : ∀ g i j, ((D'.r g i j : W.A) : R) = D.r g i j := by
        intro g i j
        rw [← hD']
        rfl
      have eψ : ∀ v i s, ((D'.ψ v i s : W.A) : R) = D.ψ v i s := by
        intro v i s
        rw [← hD']
        rfl
      refine ⟨f, RD.ext ?_ ?_⟩
      · ext g i j
        have hm : D'.r g i j ∈ W.gr (wt i j) := by
          show ((D'.r g i j : W.A) : R) ∈ W.part (wt i j)
          rw [er]
          exact hG.ent g i j
        have h := hf _ _ hm
        rw [er, hFr] at h
        exact (HahnSeries.single_injective _ h).symm
      · funext v i
        ext s
        have hm : D'.ψ v i s ∈ W.gr 0 := by
          show ((D'.ψ v i s : W.A) : R) ∈ W.part 0
          rw [eψ]
          exact hG.chr v i s
        have h := hf _ _ hm
        rw [eψ, hFψ, map_zero] at h
        exact (HahnSeries.single_injective _ h).symm
    have hlev : ∀ N : ℕ, ∃ f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1),
        D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) := by
      intro N
      haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
      haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
        co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
      exact liftNilpotent _ _ (isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ N)
        (sxNearMap (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))) hQ)
    have hval : ∀ s : W.σ, ∃ y : R', ∀ (N : ℕ) (f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
        D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) →
        f (W.zA s) = Ideal.Quotient.mk _ y := by
      intro s
      rcases hG.var s with ⟨g, i, j, c, hz, -, -⟩ | ⟨v, i, t, c, hz, -⟩
      · refine ⟨Q.r g i j - algebraMap Λ R' c, fun N f hf => ?_⟩
        have e1 : D.r g i j = ((D'.r g i j : W.A) : R) := by rw [← hD']; rfl
        have hA : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
          apply Subtype.ext
          change W.z s = _
          rw [hz, e1]
          rfl
        have e2 : f (D'.r g i j) = Ideal.Quotient.mk _ (Q.r g i j) :=
          congrArg (fun E => E.r g i j) hf
        rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
      · refine ⟨Q.ψ v i t - algebraMap Λ R' c, fun N f hf => ?_⟩
        have e1 : D.ψ v i t = ((D'.ψ v i t : W.A) : R) := by rw [← hD']; rfl
        have hA : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
          apply Subtype.ext
          change W.z s = _
          rw [hz, e1]
          rfl
        have e2 : f (D'.ψ v i t) = Ideal.Quotient.mk _ (Q.ψ v i t) :=
          congrArg (fun E => E.ψ v i t) hf
        rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
    choose y hy using hval
    choose fN hfN using hlev
    have huniq : ∀ (N : ℕ) (f f' : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
        (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
      intro N f f' h
      haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
      haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
        co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
      exact sxExtA W hG.max _ f f' h
    haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := Λ)
    obtain ⟨F, hF⟩ := sxLimPt (Λ := Λ) (maximalIdeal R') W.zA y
      (fun N => ⟨fN N, fun s => hy s N (fN N) (hfN N)⟩) huniq
    have hcomp : ∀ N, (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))).comp F = fN N := by
      intro N
      apply huniq
      intro s
      rw [AlgHom.comp_apply, hF s, hy s N (fN N) (hfN N)]
      rfl
    have hpt : ∀ (x : W.A) (q : R'), (∀ N, fN N x = Ideal.Quotient.mk _ q) → F x = q := by
      intro x q hx
      apply eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete
      intro N
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hx N, ← hcomp N]
      rfl
    refine ⟨F, ?_⟩
    apply RD.ext
    · ext g i j
      exact hpt _ _ (fun N => congrArg (fun E => E.r g i j) (hfN N))
    · funext v i
      ext t
      exact hpt _ _ (fun N => congrArg (fun E => E.ψ v i t) (hfN N))
  let ψ : (v : Φ.ι) → Fin 4 → Φ.Gv v → W.gr 0 := fun v i s =>
    ⟨D'.ψ v i s, by
      show W.A.val (D'.ψ v i s) ∈ W.part 0
      rw [hψ]
      exact hW.chr v i s⟩
  have hcont := sxContGr W hW.max (Γ := Γ)
  let C : Core Φ a :=
    { A := W.A
      B := W.gr 0
      ft := (gr_noeth Λ (ℤ × ℤ) R W hW.max).2.1
      D := D'
      rep := hrep
      cont := fun i j => hcont.1 (wt i j) (fun g => D'.r g i j)
        (fun g => by
          show W.A.val (D'.r g i j) ∈ W.part (wt i j)
          rw [hr]
          exact hW.ent g i j)
        (by
          simp only [Subalgebra.coe_val] at hr
          simp only [hr]
          exact hU.1.cont i j)
      gen := sxCoreGen hW D' hD'
      cp := cp
      cp_map := hcp1
      cp_cont := hcp2
      cp_red := hcp3
      ψ := ψ
      ψ_map := fun _ _ _ => rfl
      ψ_cont := fun v i => (sxContGr W hW.max (Γ := Φ.Gv v)).2 (ψ v i) (by
        simp only [Subalgebra.coe_val] at hψ
        simp only [ψ, hψ]
        exact hU.1.contψ v i)
      ψ_red := fun v i s => by
        have h := res_map (O := Λ) ((W.A.val).comp (IsScalarTower.toAlgHom Λ (W.gr 0) W.A)) (ψ v i s)
        rw [← h]
        have h2 : ((W.A.val).comp (IsScalarTower.toAlgHom Λ (W.gr 0) W.A)) (ψ v i s) = D.ψ v i s := hψ v i s
        rw [h2]
        exact hU.1.redψ v i s
      genB := sxGenZero hS.ok hU.1 hW D' hD' cp hcp1 ψ (fun _ _ _ => rfl)
      univ := sxNearA hU hW D' hD' }
  obtain ⟨Y⟩ := sxPreOfCore (fun v s hs => (hS.mu v s hs).1) C
  obtain ⟨hres, hlift⟩ := sxSplitRes hS
  obtain ⟨f, -⟩ := Y.univ (ResidueField Λ) _ _ hres hlift
  haveI : Nontrivial Y.A := f.toRingHom.domain_nontrivial
  obtain ⟨Y', hinj⟩ := sxPreImage Y this
  exact ⟨Y'.toSpace hinj (sxPreLine Y')⟩
