module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellOfQuotientCellRadicalPullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell

theorem projective_quot_orad (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) :
    Module.Projective O (X ⧸ (orad β : Submodule O X)) := by
  classical
  have hZ : ∀ n : ℤ, n ≠ 0 → ∀ y : X, n • y ∈ (orad β : Submodule O X) → y ∈ (orad β : Submodule O X) :=
    fun n hn y hy a z => by
      have h := hy a z
      rw [smul_comm, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hn
  have hO : ∀ a : O, a ≠ 0 → ∀ y : X, a • y ∈ (orad β : Submodule O X) → y ∈ (orad β : Submodule O X) := by
    intro a ha y hy
    have hne : (Ideal.span {a}).comap (algebraMap ℤ O) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
    refine hZ n hn0 y fun b z => ?_
    have h := hy (b * a') z
    rw [mul_smul, smul_smul a' a y, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul] at h
    exact h
  have htor : Submodule.torsion O (X ⧸ (orad β : Submodule O X)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact hO a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat O (X ⧸ (orad β : Submodule O X)) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation O (X ⧸ (orad β : Submodule O X)) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem cell_of_quot_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], IsPolyFanOn bar ψ X → (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ → InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧ genRank γ ≤ genRank δ := by
  intro O _ _ _ _ bar hCM ψ X _ _ _ _ hfan hface β hβ hp m' δ hδ hin
  classical
  have : Module.Projective O (X ⧸ (orad (O := O) β)) := projective_quot_orad O X β
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (orad (O := O) β).mkQ LinearMap.id (orad (O := O) β).mkQ_surjective
  have htt : ∀ u, (orad (O := O) β).mkQ (t u) = u := fun u => LinearMap.congr_fun ht u
  have htt' : ∀ u, (Submodule.Quotient.mk (t u) : X ⧸ (orad (O := O) β)) = u := htt
  have hπ : Function.Surjective (orad (O := O) β).mkQ := (orad (O := O) β).mkQ_surjective

  have desc : ∀ β' : LinearMap.BilinForm ℤ X, β' ∈ balForms bar X → (∀ k ∈ (orad (O := O) β), ∀ y, β' k y = 0) →
      pull (orad (O := O) β).mkQ (pull t β') = β' := by
    intro β' hb hv
    refine LinearMap.ext₂ fun a b => ?_
    have ha : a - t ((orad (O := O) β).mkQ a) ∈ (orad (O := O) β) := by
      rw [← Submodule.Quotient.mk_eq_zero (orad (O := O) β), ← Submodule.mkQ_apply, map_sub, htt, sub_self]
    have hb' : b - t ((orad (O := O) β).mkQ b) ∈ (orad (O := O) β) := by
      rw [← Submodule.Quotient.mk_eq_zero (orad (O := O) β), ← Submodule.mkQ_apply, map_sub, htt, sub_self]
    have e1 := hv _ ha b
    have e2 := hv _ hb' (t ((orad (O := O) β).mkQ a))
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1 e2
    rw [pull_apply, pull_apply, hb.1 (t _) (t _), ← e2, hb.1 b (t ((orad (O := O) β).mkQ a)), ← e1]
  have hbK : ∀ k ∈ (orad (O := O) β), ∀ y, β k y = 0 := fun k hk y => by simpa using (mem_orad.1 hk) 1 y

  have hmem : toReal β ∈ psdCone (bar := bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, d, hγ, -, hd, he⟩ := hS _ hmem
  set σ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hσdef
  have hσ : IsCell bar ψ σ := isCell_pull_equiv hγ e.symm
  have hβσ : toReal β = ∑ i, d i • toReal (σ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [LinearMap.sum_apply, hσdef] using this

  obtain ⟨Nδ, ℓδ, hNδ, hℓδ1, hℓδ2, hℓδ3⟩ := hδ.strict
  obtain ⟨Nσ, ℓσ, hNσ, hℓσ1, hℓσ2, hℓσ3⟩ := hσ.strict
  obtain ⟨hK, hKt⟩ := exists_radical_test bar (orad (O := O) β)
  let g : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (Nσ : ℤ) • (ℓδ ∘ₗ pullLin t) - (Nδ : ℤ) • ℓσ
  have hg : ∀ β', g β' = Nσ * ℓδ (pull t β') - Nδ * ℓσ β' := fun β' => by simp [g]
  set M : ℤ := ∑ j, |g (σ j)| + 1 with hM
  have hMj : ∀ j, |g (σ j)| < M := fun j => by
    have := Finset.single_le_sum (f := fun j => |g (σ j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  let hh : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := g + M • hK
  have hhv : ∀ β', hh β' = g β' + M * hK β' := fun β' => by simp [hh]
  have factA : ∀ j, hK (σ j) = 0 →
      (g (σ j) : ℝ) = Nσ * ((ℓδ (pull t (σ j)) : ℝ) - Nδ * ψ.evalZ (pull t (σ j))) := by
    intro j hj
    have hv := (hKt _ (hσ.mem j) (hσ.nonneg j)).2.1 hj
    have e1 : ψ.evalZ (σ j) = ψ.evalZ (pull t (σ j)) := by
      rw [← evalZ_pull ψ hπ (pull t (σ j)), desc _ (hσ.mem j) hv]
    rw [hg]
    push_cast
    rw [hℓσ1 j, e1]
    ring
  have hpos : ∀ j, hK (σ j) ≠ 0 → 0 < hh (σ j) := by
    intro j hj
    rw [hhv]
    have h0 := (hKt _ (hσ.mem j) (hσ.nonneg j)).1
    have h1 : 1 ≤ hK (σ j) := by omega
    have h2 := hMj j
    have hM0 : 0 ≤ M := (abs_nonneg _).trans h2.le
    have h3 := mul_le_mul_of_nonneg_left h1 hM0
    have h4 := neg_abs_le (g (σ j))
    linarith
  have hnn : ∀ j, 0 ≤ hh (σ j) := by
    intro j
    by_cases hj : hK (σ j) = 0
    · rw [hhv, hj, mul_zero, add_zero]
      have hA := factA j hj
      have h2 := hℓδ2 (pull t (σ j)) (pull_mem t (hσ.mem j)) (fun y => hσ.nonneg j _)
      have h3 : (0 : ℝ) ≤ g (σ j) := by
        rw [hA]
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
      exact_mod_cast h3
    · exact (hpos j hj).le

  set F : Finset (Fin m) := Finset.univ.filter fun j => hh (σ j) = 0 with hF
  let s : Fin F.card ↪ Fin m := (F.orderEmbOfFin rfl).toEmbedding
  have hs : ∀ j, j ∈ Set.range s ↔ hh (σ j) = 0 := fun j => by
    have : Set.range s = (F : Set (Fin m)) := Finset.range_orderEmbOfFin F rfl
    rw [this]
    simp [hF]
  have hcut : IsFaceCut σ s hh := ⟨hnn, fun j => (hs j).symm⟩
  have hσs : IsCell bar ψ (fun i => σ (s i)) := hface m F.card σ s hh hσ hcut

  have hKb : hK β = 0 := (hKt β hβ hp).2.2 hbK
  have hψβ : ψ.evalZ β = ψ.evalZ (pull t β) := by
    rw [← evalZ_pull ψ hπ (pull t β), desc β hβ hbK]
  obtain ⟨c, hc, hcβ⟩ := hin
  have hcβ1 : toReal (pull t β) = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hcβ (t a) (t b)
    simpa [LinearMap.sum_apply, htt, htt'] using this
  have hgβ : g β = 0 := by
    have e1 := intLin_eq_of_inCone ψ hσ.linear hℓσ1 hd hβσ
    have e2 := intLin_eq_of_inCone ψ hδ.linear hℓδ1 hc hcβ1
    have : (g β : ℝ) = 0 := by
      rw [hg]
      push_cast
      rw [e1, e2, hψβ]
      ring
    exact_mod_cast this
  have hhβ : hh β = 0 := by rw [hhv, hgβ, hKb]; simp
  have hsum := intLin_eq_sum_of_toReal σ d β hh hβσ
  rw [hhβ, Int.cast_zero] at hsum
  have hzero : ∀ j, d j * (hh (σ j) : ℝ) = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hd j) (by exact_mod_cast hnn j))).1 hsum.symm
    exact fun j => this j (Finset.mem_univ j)
  have hdz : ∀ j, j ∉ Set.range s → d j = 0 := fun j hj => by
    have h0 : (hh (σ j) : ℝ) ≠ 0 := by exact_mod_cast fun h => hj ((hs j).2 h)
    exact (mul_eq_zero.1 (hzero j)).resolve_right h0
  have hcone : InRCone (fun i => σ (s i)) β := by
    refine ⟨fun i => d (s i), fun i => hd _, ?_⟩
    rw [hβσ]
    exact (Fintype.sum_of_injective s s.injective _ _ (fun j hj => by rw [hdz j hj, zero_smul]) fun i => rfl).symm

  have hspan : ∀ i, ∃ k : ℕ, 0 < k ∧ k • σ (s i) ∈ Submodule.span ℤ (Set.range fun i => pull (orad (O := O) β).mkQ (δ i)) := by
    intro i
    have hj0 : hh (σ (s i)) = 0 := (hs (s i)).1 ⟨i, rfl⟩
    have hKj : hK (σ (s i)) = 0 := by
      by_contra hne
      exact (hpos _ hne).ne' hj0
    have hgj : g (σ (s i)) = 0 := by
      rw [hhv, hKj, mul_zero, add_zero] at hj0
      exact hj0
    have hA := factA _ hKj
    rw [hgj, Int.cast_zero] at hA
    have heq : (Nδ : ℝ) * ψ.evalZ (pull t (σ (s i))) = ℓδ (pull t (σ (s i))) := by
      have hN : (Nσ : ℝ) ≠ 0 := by exact_mod_cast hNσ.ne'
      have := (mul_eq_zero.1 hA.symm).resolve_left hN
      linarith
    obtain ⟨k, c', hk, hkc⟩ := hℓδ3 _ (pull_mem t (hσ.mem (s i))) (fun y => hσ.nonneg (s i) _) heq
    refine ⟨k, hk, ?_⟩
    have hv := (hKt _ (hσ.mem (s i)) (hσ.nonneg (s i))).2.1 hKj
    have e3 : k • σ (s i) = ∑ l, c' l • pull (orad (O := O) β).mkQ (δ l) := by
      have e := congrArg (pullLin (orad (O := O) β).mkQ) hkc
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_nsmul, map_sum, pullLin_apply] at e
      rw [desc _ (hσ.mem (s i)) hv] at e
      exact e
    rw [e3]
    exact Submodule.sum_mem _ fun l _ => nsmul_mem (Submodule.subset_span (Set.mem_range_self l)) _
  refine ⟨F.card, fun i => σ (s i), hσs, hcone, ?_⟩
  calc genRank (fun i => σ (s i)) ≤ genRank (fun i => pull (orad (O := O) β).mkQ (δ i)) :=
        genRank_le_of_smul_mem_span _ _ hspan
    _ = genRank δ := genRank_pull hπ δ

end GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientRadicalCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical

theorem exists_cell_quot_orad_of_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  intro O _ _ _ _ bar _hCM ψ X _ _ _ hface β _hβ _hβpsd m γ hcell hcone
  classical
  have mem_bal : ∀ {Y : Type} [AddCommGroup Y] [Module O Y] (f : LinearMap.BilinForm ℤ Y),
      f ∈ GlobalTheory.PolFan.balForms bar Y ↔
        ((∀ y z, f y z = f z y) ∧ ∀ (a : O) (y z : Y), f (a • y) z = f y (bar a • z)) :=
    fun _ => Iff.rfl
  have psd_zero : ∀ f : LinearMap.BilinForm ℤ X, f ∈ GlobalTheory.PolFan.balForms bar X →
      (∀ y, 0 ≤ f y y) → ∀ x, f x x = 0 → ∀ y, f x y = 0 := by
    intro f hf hfp x hx y
    have hsym : f y x = f x y := ((mem_bal f).1 hf).1 y x
    by_contra hne
    have expand : ∀ n : ℤ, f (n • x + y) (n • x + y) =
        n * n * f x x + n * f x y + n * f y x + f y y := by
      intro n
      simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    have key := hfp ((-(f y y + 1) * f x y) • x + y)
    rw [expand, hx, hsym] at key
    have h1 : 0 < f x y * f x y := mul_self_pos.2 hne
    have h2 : 1 ≤ f x y * f x y := by simpa using Int.add_one_le_iff.2 h1
    have h0 := hfp y
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ f y y + 1) (by linarith : (0:ℤ) ≤ f x y * f x y - 1)]
  obtain ⟨c, hc0, hcsum⟩ := hcone
  have hval : ∀ x y, ((β x y : ℤ) : ℝ) = ∑ i, c i * ((γ i x y : ℤ) : ℝ) := by
    intro x y
    have := congrArg (fun L : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => L x y) hcsum
    simpa [GlobalTheory.PolFan.toReal] using this
  set K : Submodule O X := GlobalTheory.PolFan.CarDim.orad β with hK
  have hKβ : ∀ x ∈ K, β x x = 0 := by
    intro x hx
    have := (GlobalTheory.PolFan.CarDim.mem_orad (O := O)).1 hx 1 x
    simpa using this
  let P : Fin m → Prop := fun j => ∀ x ∈ K, ∀ y, γ j x y = 0
  have hpos : ∀ j, 0 < c j → P j := by
    intro j hcj x hx
    apply psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x
    have hsum : ∑ i, c i * ((γ i x x : ℤ) : ℝ) = 0 := by
      rw [← hval, hKβ x hx]
      simp
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ c i * ((γ i x x : ℤ) : ℝ) := fun i _ =>
      mul_nonneg (hc0 i) (by exact_mod_cast hcell.nonneg i x)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (Finset.mem_univ j)
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h hcj.ne'
    · exact_mod_cast h
  have hw : ∀ j, ∃ x ∈ K, (¬ P j → 0 < γ j x x) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, K.zero_mem, fun h => absurd hj h⟩
    · simp only [P, not_forall] at hj
      obtain ⟨x, hx, y, hxy⟩ := hj
      refine ⟨x, hx, fun _ => ?_⟩
      rcases (hcell.nonneg j x).lt_or_eq with h | h
      · exact h
      · exact absurd (psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x h.symm y) hxy
  choose w hwK hwpos using hw
  let h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ :=
    { toFun := fun f => ∑ j, f (w j) (w j)
      map_add' := fun f g => by simp [Finset.sum_add_distrib]
      map_smul' := fun a f => by simp [Finset.mul_sum] }
  have hh : ∀ f, h f = ∑ j, f (w j) (w j) := fun _ => rfl
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsT : ∀ j, j ∈ Set.range s ↔ P j := by
    intro j
    have hr : Set.range s = (T : Set (Fin m)) := Finset.range_orderEmbOfFin T rfl
    rw [hr]
    simp [T]
  have hPs : ∀ i, P (s i) := fun i => (hsT (s i)).1 ⟨i, rfl⟩
  have hfc : GlobalTheory.PolFan.IsFaceCut γ s h := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [hh]
      exact Finset.sum_nonneg fun i _ => hcell.nonneg j (w i)
    · rw [hsT, hh]
      constructor
      · intro h0
        by_contra hj
        have hnn : ∀ i ∈ Finset.univ, 0 ≤ γ j (w i) (w i) := fun i _ => hcell.nonneg j (w i)
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
        exact (hwpos j hj).ne' this
      · intro hj
        exact Finset.sum_eq_zero fun i _ => hj (w i) (hwK i) (w i)
  have hcell' := hface m T.card γ s h hcell hfc
  have hvanl : ∀ i, ∀ x ∈ K, ∀ y, γ (s i) x y = 0 := fun i => hPs i
  have hvanr : ∀ i, ∀ x y, y ∈ K → γ (s i) x y = 0 := by
    intro i x y hy
    rw [((mem_bal _).1 (hcell.mem (s i))).1 x y]
    exact hPs i y hy x
  choose δ hδ using fun i =>
    GlobalTheory.PolFan.CarDim.exists_pull_mkQ_eq_of_vanish K (γ (s i)) (hvanl i) (hvanr i)
  have hr : Function.Surjective K.mkQ := K.mkQ_surjective
  have hδap : ∀ i x y, δ i (K.mkQ x) (K.mkQ y) = γ (s i) x y := by
    intro i x y
    rw [← hδ i]
    rfl
  have heZ : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K),
      ψ.evalZ (GlobalTheory.PolFan.pull K.mkQ f) = ψ.evalZ f := by
    intro f
    exact ψ.eval_comp hr (fun a b => ((f a b : ℤ) : ℝ))
  have hpullbal : ∀ f ∈ GlobalTheory.PolFan.balForms bar (X ⧸ K),
      GlobalTheory.PolFan.pull K.mkQ f ∈ GlobalTheory.PolFan.balForms bar X := by
    intro f hf
    obtain ⟨hs, hb⟩ := (mem_bal f).1 hf
    refine (mem_bal _).2 ⟨fun y z => hs (K.mkQ y) (K.mkQ z), fun a y z => ?_⟩
    show f (K.mkQ (a • y)) (K.mkQ z) = f (K.mkQ y) (K.mkQ (bar a • z))
    rw [LinearMap.map_smul, LinearMap.map_smul]
    exact hb a (K.mkQ y) (K.mkQ z)
  have hpullpsd : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K), (∀ q, 0 ≤ f q q) →
      ∀ y, 0 ≤ GlobalTheory.PolFan.pull K.mkQ f y y :=
    fun f hf y => hf (K.mkQ y)
  have hfun : (fun i => GlobalTheory.PolFan.pull K.mkQ (δ i)) = fun i => γ (s i) := funext hδ
  refine ⟨T.card, δ, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i q => ?_, ?_, ?_⟩
    · refine (mem_bal _).2 ⟨fun a b => ?_, fun a u v => ?_⟩
      · obtain ⟨x, rfl⟩ := hr a
        obtain ⟨y, rfl⟩ := hr b
        rw [hδap, hδap]
        exact ((mem_bal _).1 (hcell.mem (s i))).1 x y
      · obtain ⟨x, rfl⟩ := hr u
        obtain ⟨y, rfl⟩ := hr v
        rw [← LinearMap.map_smul, ← LinearMap.map_smul, hδap, hδap]
        exact ((mem_bal _).1 (hcell.mem (s i))).2 a x y
    · obtain ⟨y, rfl⟩ := hr q
      rw [hδap]
      exact hcell.nonneg (s i) y
    · intro c hc
      have key := hcell'.linear.eval_eq_sum (X₁ := X ⧸ K) hr
        (B := fun a b => ∑ i, c i * ((δ i a b : ℤ) : ℝ)) hc (fun a b => by simp only [hδap])
      rw [key]
      refine Finset.sum_congr rfl fun i _ => ?_
      show c i * ψ.evalZ (γ (s i)) = c i * ψ.evalZ (δ i)
      rw [← hδ i, heZ]
    · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hcell'.strict
      refine ⟨N, ℓ.comp (GlobalTheory.PolFan.CarDim.pullLin K.mkQ), hN, fun i => ?_,
        fun β' hb hp => ?_, fun β' hb hp heq => ?_⟩
      · have h1i : ((ℓ (γ (s i)) : ℤ) : ℝ) = (N : ℝ) * ψ.evalZ (γ (s i)) := h1 i
        rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, hδ i, h1i, ← hδ i, heZ]
      · rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ]
        exact h2 _ (hpullbal β' hb) (hpullpsd β' hp)
      · rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ] at heq
        obtain ⟨k, c', hk, hkc⟩ := h3 _ (hpullbal β' hb) (hpullpsd β' hp) heq
        refine ⟨k, c', hk, ?_⟩
        have hkc' : k • GlobalTheory.PolFan.pull K.mkQ β' = ∑ i, c' i • γ (s i) := hkc
        apply GlobalTheory.PolFan.CarDim.pullLin_injective hr
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_nsmul, map_zsmul, LinearMap.map_smul_of_tower, map_sum,
          GlobalTheory.PolFan.CarDim.pullLin_apply]
        rw [hkc']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hδ i]
  · rw [hfun]
    simp only [GlobalTheory.PolFan.InRCone]
    refine ⟨fun i => c (s i), fun i => hc0 _, ?_⟩
    rw [hcsum]
    have hmap : Finset.univ.map s = T := Finset.map_orderEmbOfFin_univ T rfl
    have e1 : (∑ i, c (s i) • GlobalTheory.PolFan.toReal (γ (s i))) =
        ∑ j ∈ T, c j • GlobalTheory.PolFan.toReal (γ j) := by
      exact (Finset.sum_map Finset.univ s (fun j => c j • GlobalTheory.PolFan.toReal (γ j))).symm.trans
        (by rw [hmap])
    rw [e1]
    symm
    apply Finset.sum_filter_of_ne
    intro j _ hne
    by_contra hj
    apply hne
    have hcj : c j = 0 := by
      rcases (hc0 j).lt_or_eq with h' | h'
      · exact absurd (hpos j h') hj
      · exact h'.symm
    rw [hcj, zero_smul]
  · rw [← GlobalTheory.PolFan.CarDim.genRank_pull hr δ, hfun]
    unfold GlobalTheory.PolFan.genRank
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) :=
      Module.Finite.span_of_finite ℤ (Set.finite_range γ)
    exact Submodule.finrank_mono
      (Submodule.span_mono (Set.range_comp_subset_range s γ))

end GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsBalancedFormsDominating
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem contact_inter_rcone_spanned : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι]
    (a : ι → X) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) →
    ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧
      (∀ i, toReal (γ i) ∈ contact bar a) ∧ ∀ B ∈ contact bar a, B ∈ rcone u → B ∈ rcone γ := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a m u hsym hpsd
  classical
  choose F hF using fun i => isMin2_iff_finite X m u (a i) hpsd
  let A : Set (Fin m → ℤ) := ⋃ i, (fun (x : X) (k : Fin m) =>
    u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) '' (F i : Set X)
  let V : Set (Fin m → ℤ) := Set.range fun (p : O × X × X) (k : Fin m) =>
    u k (p.1 • p.2.1) p.2.2 - u k p.2.1 (bar p.1 • p.2.2)
  have hA : A.Finite := Set.finite_iUnion fun i => (F i).finite_toSet.image _
  obtain ⟨r, v, hv, -⟩ := _root_.GlobalTheory.MinkWeylReal.cone_orthant_fg m A V hA
  have hval : ∀ (t : Fin m → ℝ) (y z : X), (∑ k, t k • toReal (u k)) y z = ∑ k, t k * (u k y z : ℝ) :=
    fun t y z => by simp [LinearMap.sum_apply]
  have hdiff : ∀ (t : Fin m → ℝ) (p p' q q' : X), ∑ k, (((u k p p' - u k q q' : ℤ)) : ℝ) * t k =
      (∑ k, t k • toReal (u k)) p p' - (∑ k, t k • toReal (u k)) q q' := fun t p p' q q' => by
    rw [hval, hval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  have hAiff : ∀ t : Fin m → ℝ, (∀ k, 0 ≤ t k) → ((∀ i, IsMin2 (∑ k, t k • toReal (u k)) (a i)) ↔
      ∀ b ∈ A, ∑ k, (b k : ℝ) * t k ≤ 0) := fun t ht => by
    constructor
    · intro h b hb
      obtain ⟨i, x, -, rfl⟩ : ∃ i, ∃ x ∈ (F i : Set X), (fun k : Fin m =>
          u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) = b := by
        simpa [A] using hb
      rw [hdiff]
      linarith [h i x]
    · intro h i
      refine (hF i _ ⟨t, ht, rfl⟩).2 fun x hx => ?_
      have := h _ (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)
      rw [hdiff] at this
      linarith
  have hViff : ∀ t : Fin m → ℝ, (∀ (c : O) (y z : X), (∑ k, t k • toReal (u k)) (c • y) z =
      (∑ k, t k • toReal (u k)) y (bar c • z)) ↔ ∀ b ∈ V, ∑ k, (b k : ℝ) * t k = 0 := fun t => by
    constructor
    · rintro h _ ⟨⟨c, y, z⟩, rfl⟩
      simp only []
      rw [hdiff, h, sub_self]
    · intro h c y z
      have := h _ ⟨(c, y, z), rfl⟩
      simp only [] at this
      rw [hdiff] at this
      linarith
  let γ : Fin r → LinearMap.BilinForm ℤ X := fun s => ∑ k, v s k • u k
  have hγ : ∀ s y z, γ s y z = ∑ k, (v s k : ℤ) * u k y z := fun s y z => by
    simp [γ, LinearMap.sum_apply]
  have hγr : ∀ s, toReal (γ s) = ∑ k, (v s k : ℝ) • toReal (u k) := fun s => LinearMap.ext₂ fun y z => by
    rw [hval, toReal_apply, hγ]
    push_cast
    rfl
  have hvs : ∀ s, (∀ k, (0 : ℝ) ≤ v s k) ∧ (∀ b ∈ A, ∑ k, (b k : ℝ) * (v s k : ℝ) ≤ 0) ∧
      (∀ b ∈ V, ∑ k, (b k : ℝ) * (v s k : ℝ) = 0) := fun s => by
    refine (hv fun k => (v s k : ℝ)).2 ⟨Pi.single s 1, fun j => ?_, ?_⟩
    · by_cases h : j = s
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · rw [Finset.sum_eq_single s (fun j _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
      simp
  have hbal : ∀ s, γ s ∈ balForms bar X := fun s => by
    refine mem_balForms.2 ⟨fun y z => ?_, fun c y z => ?_⟩
    · simp only [hγ, hsym _ y z]
    · have := (hViff _).2 (hvs s).2.2 c y z
      rw [← hγr] at this
      simpa using this
  have hnn : ∀ s y, 0 ≤ γ s y y := fun s y => by
    rw [hγ]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Int.natCast_nonneg _) (hpsd k y)
  refine ⟨r, γ, hbal, hnn, fun s => ⟨?_, fun i => ?_⟩, ?_⟩
  · simpa using GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![γ s] ![1] (by simpa using hbal s) (by simpa using hnn s) (by simp)
  · rw [hγr]
    exact (hAiff _ (hvs s).1).2 (hvs s).2.1 i
  · rintro _ hB ⟨t, ht, rfl⟩
    have hre := mem_realForms_of_mem_psdCone hB.1
    obtain ⟨c, hc, rfl⟩ := (hv t).1 ⟨ht, (hAiff t ht).1 hB.2, (hViff t).1 hre.2⟩
    refine ⟨c, hc, LinearMap.ext₂ fun y z => ?_⟩
    rw [hval]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hγ, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

