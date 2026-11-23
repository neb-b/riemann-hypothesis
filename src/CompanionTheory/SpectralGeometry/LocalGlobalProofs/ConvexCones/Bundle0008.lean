module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellOfQuotientCellRadicalPullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.EvalPullbackSemilinearSurjective
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval

open GlobalTheory.PolFan.OrbMark

theorem eval_pull_semilinear_of_isTwG : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
    ∀ {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
      (τ : O ≃+* O), τ w0 = w0 → ∀ (f : X →+ Y), Function.Surjective f → (∀ (a : O) (x : X), f (a • x) = τ a • f x) →
      ∀ B : Y → Y → ℝ, φ.eval X (fun x y => B (f x) (f y)) = φ.eval Y B := by
  intro O _ _ _ _ bar w0 _ φ hφ X Y _ _ _ _ _ _ τ hτ f hf hsl B
  obtain ⟨n, πX, hπX⟩ := Module.Finite.exists_fin' O X
  let g : (Fin n → O) →ₗ[O] Y :=
    { toFun := fun a => f (πX (twv τ.symm a))
      map_add' := fun a b => by
        show f (πX (twv τ.symm (a + b))) = f (πX (twv τ.symm a)) + f (πX (twv τ.symm b))
        have hadd : twv τ.symm (a + b) = twv τ.symm a + twv τ.symm b := by
          funext i
          simp [twv_apply]
        rw [hadd, map_add (f := _), map_add (f := _)]
      map_smul' := fun c a => by
        show f (πX (twv τ.symm (c • a))) = c • f (πX (twv τ.symm a))
        rw [twv_smul, map_smul, hsl, RingEquiv.apply_symm_apply] }
  have hg_apply : ∀ a, g a = f (πX (twv τ.symm a)) := fun _ => rfl
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, rfl⟩ := hπX x
    exact ⟨twv τ a, by rw [hg_apply, twv_symm_twv]⟩
  have key : ∀ a : Fin n → O, g (fun i => τ (a i)) = f (πX a) := by
    intro a
    rw [hg_apply]
    congr 2
    funext i
    simp [twv_apply]
  rw [φ.eval_eq hπX, φ.eval_eq hg, ← hφ τ hτ n (fun a b => B (g a) (g b))]
  congr 1
  funext a b
  show B (f (πX a)) (f (πX b)) = B (g (fun i => τ (a i))) (g (fun i => τ (b i)))
  rw [key a, key b]

end GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsCarrierDimensionLabel
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension

theorem exists_cell {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {ψ : InvFun O} {X : Type}
    [AddCommGroup X] [Module O X] [Module.Finite O X] (hfan : IsPolyFanOn bar ψ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β := by
  have hmem : toReal β ∈ psdCone (bar := bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hS _ hmem
  refine ⟨m, fun i => pull e.symm.toLinearMap (γ i), isCell_pull_equiv hγ e.symm, c, hc, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
  simpa [LinearMap.sum_apply] using this

theorem exists_isCarrierDim : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ lab : InvFun O, IsTwG w0 lab ∧ IsCarrierDim bar q ψ lab := by
  intro O _ _ _ _ bar w0 hb q ψ hD hψ htw
  refine ⟨carFun bar ψ, _root_.GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun O bar w0 hb ψ htw, ?_⟩
  intro X _ _ _ _ hX β hβ hp
  have hfan := hψ X hX
  have hface := _root_.GlobalTheory.CompanionTheory.Ar.Fan.CellFaces.isCell_comp O bar hb ψ X hfan (hD X)
  rw [evalZ_carFun hβ hp]
  congr 1
  obtain ⟨m₀, γ₀, hγ₀, hin₀⟩ := exists_cell hfan hβ hp
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}.Nonempty := ⟨_, m₀, γ₀, hγ₀, hin₀, rfl⟩
  apply le_antisymm
  · obtain ⟨m, γ, h1, h2, h3⟩ := Nat.sInf_mem hne
    obtain ⟨m', δ, k1, k2, k3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical.exists_cell_quot_orad_of_inRCone O bar hb ψ X hface β hβ hp m γ h1 h2
    exact (Nat.sInf_le (show genRank δ ∈ cdimSet bar ψ X (orad β) β from ⟨m', δ, k1, k2, rfl⟩)).trans (k3.trans h3.le)
  · have hne' : (cdimSet bar ψ X (orad β) β).Nonempty := by
      obtain ⟨m', δ, k1, k2, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical.exists_cell_quot_orad_of_inRCone O bar hb ψ X hface β hβ hp m₀ γ₀ hγ₀ hin₀
      exact ⟨_, m', δ, k1, k2, rfl⟩
    obtain ⟨m', δ, h1, h2, h3⟩ := Nat.sInf_mem hne'
    obtain ⟨m, γ, k1, k2, k3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell O bar hb ψ X hfan hface β hβ hp m' δ h1 h2
    unfold cdimQ
    rw [← h3]
    exact (Nat.sInf_le (show genRank γ ∈ {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      InRCone γ β ∧ genRank γ = k} from ⟨m, γ, k1, k2, rfl⟩)).trans k3

end GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFiniteBelowModTwo
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_finite_below_mod_two {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] {m : ℕ}
    (f : X → Fin m → ℕ) :
    ∃ G : Set X, G.Finite ∧ ∀ y, ∃ y' ∈ G, (∃ x : X, y' = y + (x + x)) ∧ f y' ≤ f y := by
  classical
  have hmin : ∀ (V : Set (Fin m → ℕ)) (a : Fin m → ℕ), a ∈ V → ∃ v, Minimal (· ∈ V) v ∧ v ≤ a := by
    intro V a ha
    obtain ⟨v, ⟨hvV, hva⟩, hvmin⟩ := wellFounded_lt.has_min {w | w ∈ V ∧ w ≤ a} ⟨a, ha, le_rfl⟩
    refine ⟨v, ⟨hvV, fun w hwV hwv => ?_⟩, hva⟩
    by_contra hne
    exact hvmin w ⟨hwV, hwv.trans hva⟩ (lt_of_le_of_ne hwv fun h => hne (le_of_eq h.symm))
  set e := (Module.finBasis ℤ X).equivFun with he
  have key : ∀ y : X, ∃ x : X,
      e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y + (x + x) := by
    intro y
    refine ⟨e.symm (fun i => -(e y i / 2)), ?_⟩
    apply e.injective
    rw [map_add (f := _), map_add (f := _), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    funext i
    simp only [ZMod.val_intCast, Pi.add_apply, Nat.cast_ofNat]
    rw [Int.emod_def]
    ring
  let red : X → (Fin (Module.finrank ℤ X) → ZMod 2) := fun y i => ((e y i : ℤ) : ZMod 2)
  have hred : ∀ y y' : X, red y' = red y → ∃ x : X, y' = y + (x + x) := by
    intro y y' h
    obtain ⟨x1, h1⟩ := key y
    obtain ⟨x2, h2⟩ := key y'
    refine ⟨x1 - x2, ?_⟩
    have hh : (fun i => ((e y' i : ℤ) : ZMod 2)) = (fun i => ((e y i : ℤ) : ZMod 2)) := h
    have h2' : e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y' + (x2 + x2) := by
      rw [← h2]
      congr 1
      funext i
      rw [congrFun hh i]
    have h3 : y' + (x2 + x2) = y + (x1 + x1) := h2'.symm.trans h1
    rw [eq_sub_of_add_eq h3]
    abel
  let V : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ) := fun ε => f '' {y | red y = ε}
  let M : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ) := fun ε => {v | Minimal (· ∈ V ε) v}
  have hMfin : ∀ ε, (M ε).Finite := fun ε =>
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain fun x => x ∈ V ε)
  let pick : (Fin (Module.finrank ℤ X) → ZMod 2) → (Fin m → ℕ) → X := fun ε v =>
    if h : ∃ y, red y = ε ∧ f y = v then h.choose else 0
  refine ⟨⋃ ε, pick ε '' M ε, Set.finite_iUnion fun ε => (hMfin ε).image _, fun y => ?_⟩
  obtain ⟨v, hvM, hvle⟩ := hmin (V (red y)) (f y) ⟨y, rfl, rfl⟩
  have hex : ∃ w, red w = red y ∧ f w = v := by
    obtain ⟨w, hw, hwv⟩ := hvM.1
    exact ⟨w, hw, hwv⟩
  have hpick : red (pick (red y) v) = red y ∧ f (pick (red y) v) = v := by
    dsimp only [pick]
    rw [dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨pick (red y) v, Set.mem_iUnion.mpr ⟨red y, v, hvM, rfl⟩, hred y _ hpick.1, ?_⟩
  rw [hpick.2]
  exact hvle

theorem finite_isMin2 : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (m : ℕ)
    (P : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) →
    ∃ F : Set X, F.Finite ∧ ∀ B ∈ rcone P, IsPosDef B → ∀ y, IsMin2 B y → y ∈ F := by
  intro X _ _ _ m P hsym hnn
  classical
  obtain ⟨G, hG, hGy⟩ := exists_finite_below_mod_two (fun y i => (P i y y).toNat)
  set C : ℤ := ∑ g ∈ hG.toFinset, ∑ i, P i g g with hC
  let Q : Finset (Fin m) → LinearMap.BilinForm ℤ X := fun S => ∑ i ∈ S, P i
  have hQ : ∀ S z w, Q S z w = ∑ i ∈ S, P i z w := by
    intro S z w
    simp [Q, LinearMap.sum_apply]
  refine ⟨⋃ S : Finset (Fin m), if (∀ y : X, y ≠ 0 → 0 < Q S y y) then {y | Q S y y ≤ S.card * C} else ∅,
    ?_, ?_⟩
  · refine Set.finite_iUnion fun S => ?_
    split_ifs with hpos
    · exact _root_.GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite X (Q S) (fun y z => by
        rw [hQ, hQ]
        exact Finset.sum_congr rfl fun i _ => hsym i y z) hpos _
    · exact Set.finite_empty
  · rintro B ⟨t, ht0, rfl⟩ hB y hy
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin m), S = Finset.univ.filter (fun i => 0 < t i) := ⟨_, rfl⟩
    have hBapp : ∀ z w : X, (∑ i, t i • GlobalTheory.PolFan.toReal (P i)) z w = ∑ i, t i * ((P i z w : ℤ) : ℝ) := by
      intro z w
      simp [GlobalTheory.PolFan.toReal, LinearMap.sum_apply]
    have hBpos : ∀ z : X, z ≠ 0 → 0 < ∑ i, t i * ((P i z z : ℤ) : ℝ) := by
      intro z hz
      have h1 := hB 1 ![z] (linearIndependent_unique_iff.mpr (by simpa using hz)) ![1] (by simp)
      simpa [hBapp] using h1
    have hterm : ∀ z : X, ∑ i, t i * ((P i z z : ℤ) : ℝ) = ∑ i ∈ S, t i * ((P i z z : ℤ) : ℝ) := by
      intro z
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · have h0 : t i = 0 := le_antisymm (not_lt.mp h) (ht0 i)
        simp [h0]
    have hpos : ∀ z : X, z ≠ 0 → 0 < Q S z z := by
      intro z hz
      rw [hQ]
      by_contra hle
      have h0 : ∑ i ∈ S, P i z z = 0 := le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun i _ => hnn i z)
      have hzero : ∀ i ∈ S, P i z z = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i z).mp h0
      have h1 := hBpos z hz
      rw [hterm, Finset.sum_eq_zero fun i hi => by rw [hzero i hi]; simp] at h1
      exact lt_irrefl _ h1
    obtain ⟨y', hy'G, ⟨x, hx⟩, hle⟩ := hGy y
    have hle' : ∀ i, P i y' y' ≤ P i y y := fun i => by
      have h1 : (P i y' y').toNat ≤ (P i y y).toNat := hle i
      have h2 := hnn i y
      have h3 := hnn i y'
      omega
    have hmin : ∑ i, t i * ((P i y y : ℤ) : ℝ) ≤ ∑ i, t i * ((P i y' y' : ℤ) : ℝ) := by
      have h1 := hy x
      rw [← hx, hBapp, hBapp] at h1
      exact h1
    have hd : ∀ i ∈ Finset.univ, 0 ≤ t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ)) := fun i _ =>
      mul_nonneg (ht0 i) (sub_nonneg.mpr (by exact_mod_cast hle' i))
    have hsum : ∑ i, t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ)) = 0 := by
      apply le_antisymm
      · simp only [mul_sub, Finset.sum_sub_distrib]
        linarith
      · exact Finset.sum_nonneg hd
    have heq : ∀ i ∈ S, P i y y ≤ P i y' y' := by
      intro i hi
      have hi0 := (Finset.sum_eq_zero_iff_of_nonneg hd).mp hsum i (Finset.mem_univ i)
      rw [hS, Finset.mem_filter] at hi
      have h4 : ((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp hi0 with h | h
        · exact absurd h hi.2.ne'
        · exact h
      have h5 : ((P i y y : ℤ) : ℝ) ≤ ((P i y' y' : ℤ) : ℝ) := by linarith
      exact_mod_cast h5
    have hbound : ∀ i, P i y' y' ≤ C := by
      intro i
      rw [hC]
      calc P i y' y' ≤ ∑ j, P j y' y' := Finset.single_le_sum (fun j _ => hnn j y') (Finset.mem_univ i)
        _ ≤ ∑ g ∈ hG.toFinset, ∑ j, P j g g :=
          Finset.single_le_sum (f := fun g => ∑ j, P j g g)
            (fun g _ => Finset.sum_nonneg fun j _ => hnn j g) (hG.mem_toFinset.mpr hy'G)
    refine Set.mem_iUnion.mpr ⟨S, ?_⟩
    rw [if_pos hpos]
    show Q S y y ≤ S.card * C
    rw [hQ]
    calc ∑ i ∈ S, P i y y ≤ ∑ i ∈ S, C := Finset.sum_le_sum fun i hi => (heq i hi).trans (hbound i)
      _ = S.card * C := by rw [Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsStarOfClauses
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan GlobalTheory.PolFan.StarCells

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses

theorem isStarOf_of_clauses : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf bar q ψ w ψ' := by
  intro O _ _ _ _ bar _ q ψ w ψ' hψ hw h1 h2
  refine ⟨h1, h2, ?_⟩

  intro X _ _ _ _ hX n γ' hγ'
  set B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ j, (1 : ℝ) • toReal (γ' j) with hBdef
  have hB : B ∈ psdCone (bar := bar) (X := X) :=
    ConeSub.sum_smul_toReal_mem_psdCone O bar X n γ' _ hγ'.mem hγ'.nonneg fun _ => zero_le_one
  obtain ⟨S, -, hfin⟩ := (hψ X hX).finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hfin B hB
  set δ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hδdef
  have hδ : IsCell bar ψ δ := CarDim.isCell_pull_equiv hγ e.symm
  have hBδ : B = ∑ i, c i • toReal (δ i) := by
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simp only [pullR_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, toReal_apply, smul_eq_mul] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hδdef, pull_apply,
      LinearEquiv.coe_coe]
    exact this
  have key : ∀ (k : ℕ) (σ : Fin k → LinearMap.BilinForm ℤ X), IsCell bar ψ' σ → B ∈ rcone σ →
      ∀ j, InRCone σ (γ' j) := by
    rintro k σ hσ ⟨t, ht, hBt⟩ j
    obtain ⟨kk, d, hk, hkd⟩ := inCone_of_strict hσ.strict hσ.linear hγ'.mem hγ'.nonneg (a := fun _ => 1) (b := t)
      (fun _ => zero_le_one) ht ((linearOn_iff ψ' γ').1 hγ'.linear _ fun _ => zero_le_one) hBt j one_ne_zero
    exact inRCone_of_nsmul hk hkd
  by_cases hc0 : ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ InRCone δ β ∧ w.evalZ β = 1
  · obtain ⟨β₀, hβ₀, hβ₀p, hin, hw1⟩ := hc0
    have hne : β₀ ≠ 0 := by
      intro h0
      have := (hw X hX).2.1 β₀ hβ₀ hβ₀p hw1 2 0 (by simp [h0])
      omega
    obtain ⟨m', s, h, hfc, hpos, hBc⟩ :=
      _root_.GlobalTheory.StarCover.star_cover X m δ β₀ B (fun i => (hδ.mem i).1) hδ.nonneg hne hin ⟨c, hc, hBδ⟩
    exact Or.inr ⟨m, δ, β₀, m', s, h, hδ, hβ₀, hβ₀p, hw1, hin, hfc, hpos,
      key _ _ (h2 X hX m δ hδ β₀ hβ₀ hβ₀p hw1 hin m' s h hfc hpos) hBc⟩
  · push_neg at hc0
    have h0 : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β = 0 := fun β hβ hp hi =>
      ((hw X hX).1 β hβ hp).resolve_right (hc0 β hβ hp hi)
    exact Or.inl ⟨m, δ, hδ, h0, key _ _ (h1 X hX m δ hδ h0) ⟨c, hc, hBδ⟩⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsStarOfFiniteCover
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarFiniteCover

private theorem inRCone_mono_of_range_subset {X : Type} [AddCommGroup X] {m n : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin n → LinearMap.BilinForm ℤ X)
    (hsub : Set.range γ' ⊆ Set.range γ) {β : LinearMap.BilinForm ℤ X}
    (h : GlobalTheory.PolFan.InRCone γ' β) : GlobalTheory.PolFan.InRCone γ β := by
  classical
  obtain ⟨c, hc, hβ⟩ := h
  choose j hj using fun i => hsub (Set.mem_range_self i)
  refine ⟨fun a => ∑ i ∈ Finset.univ.filter (fun i => j i = a), c i,
    fun a => Finset.sum_nonneg fun i _ => hc i, ?_⟩
  rw [hβ]
  symm
  calc ∑ a, (∑ i ∈ Finset.univ.filter (fun i => j i = a), c i) • GlobalTheory.PolFan.toReal (γ a)
      = ∑ a, ∑ i ∈ Finset.univ.filter (fun i => j i = a), c i • GlobalTheory.PolFan.toReal (γ (j i)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, c i • GlobalTheory.PolFan.toReal (γ (j i)) := Finset.sum_fiberwise _ _ _
    _ = ∑ i, c i • GlobalTheory.PolFan.toReal (γ' i) := by simp_rw [hj]

theorem isStarOf_finite_cover : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → IsStarOf bar q ψ w ψ' →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank O X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := bar) (X := X),
      ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar ψ' γ ∧
        (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro O _ _ _ _ bar hO q ψ w ψ' hψ hC hStar X _ _ _ _ hq
  classical
  obtain ⟨hS1, hS2, -⟩ := hStar
  obtain ⟨S0, hS0, hcov⟩ := (hψ X hq).finite
  obtain ⟨ch, hch⟩ : ∃ ch : Set (LinearMap.BilinForm ℤ X) → LinearMap.BilinForm ℤ X,
      ∀ T : Set (LinearMap.BilinForm ℤ X),
        (∃ β, β ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧
          ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧
            Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ β) →
        (ch T ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ ch T y y) ∧ w.evalZ (ch T) = 1 ∧
          ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧
            Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ (ch T)) :=
    ⟨fun T => @Classical.epsilon _ ⟨0⟩ (fun β => β ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧
        w.evalZ β = 1 ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧
          Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ β),
      fun T h => Classical.epsilon_spec h⟩
  refine ⟨S0 ∪ ch '' {T | T ⊆ S0}, hS0.union (hS0.finite_subsets.image _), ?_⟩
  intro B hB
  obtain ⟨e, m, γ, c, hcell, hγS, hc, hBe⟩ := hcov B hB
  by_cases hz : ∀ β ∈ GlobalTheory.PolFan.balForms bar X, (∀ y, 0 ≤ β y y) → GlobalTheory.PolFan.InRCone γ β → w.evalZ β = 0
  · exact ⟨e, m, γ, c, hS1 X hq m γ hcell hz, fun i => Set.mem_union_left _ (hγS i), hc, hBe⟩
  · push Not at hz
    obtain ⟨β₀, hbal, hpsd, hin, hne⟩ := hz
    have hw1 : w.evalZ β₀ = 1 := ((hC X hq).1 β₀ hbal hpsd).resolve_left hne
    have hβne : β₀ ≠ 0 := by
      intro h0
      have h21 := (hC X hq).2.1 β₀ hbal hpsd hw1 2 0 (by rw [h0, smul_zero])
      omega
    have hsymm : ∀ (i : Fin m) (y z : X), (γ i) y z = (γ i) z y := fun i =>
      (show (∀ y z : X, (γ i) y z = (γ i) z y) ∧ _ from hcell.mem i).1
    have hBr : GlobalTheory.PolFan.pullR e.toLinearMap B ∈ GlobalTheory.PolCell.rcone γ := by
      simp only [GlobalTheory.PolCell.rcone, Set.mem_ofPred_eq]
      exact ⟨c, hc, hBe⟩
    obtain ⟨m', s, h, hcut, hpos, hB'⟩ :=
      _root_.GlobalTheory.StarCover.star_cover X m γ β₀ (GlobalTheory.PolFan.pullR e.toLinearMap B) hsymm hcell.nonneg hβne hin hBr
    obtain ⟨t, ht, htB⟩ := hB'
    refine ⟨e, m' + 1, Fin.cons β₀ fun j => γ (s j), t,
      hS2 X hq m γ hcell β₀ hbal hpsd hw1 hin m' s h hcut hpos, ?_, ht, htB⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]
      refine Set.mem_union_right _ ⟨Set.range γ, ?_, ?_⟩
      · rintro _ ⟨i, rfl⟩
        exact hγS i
      · obtain ⟨hb', hp', hw', m'', γ'', hcell'', hrange, hin''⟩ :=
          hch (Set.range γ) ⟨β₀, hbal, hpsd, hw1, m, γ, hcell, rfl, hin⟩
        have hin2 : GlobalTheory.PolFan.InRCone γ (ch (Set.range γ)) :=
          inRCone_mono_of_range_subset γ γ'' hrange.le hin''
        exact (hC X hq).2.2 m γ hcell _ hb' hp' β₀ hbal hpsd hw' hw1 hin2 hin
    · rw [Fin.cons_succ]
      exact Set.mem_union_left _ (hγS (s j))

end GlobalTheory.CompanionTheory.Ar.Fan.StarFiniteCover
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MaxMultiplicityLtTop
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite


open GlobalTheory.PolFan.MultBound in
theorem maxMult_lt_top : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O), IsPolyFan bar q φ → maxMult bar q φ < ⊤ := by
  intro O _ _ _ _ bar hCM q φ hφ
  obtain ⟨n, R, hR, hcls⟩ := hCM.classes q
  have hC := fun k : Fin n =>
    haveI := (hR k).1
    haveI := (hR k).2.1
    GlobalTheory.PolFan.MultBound.perModule (hφ (R k) (hR k).2.2) (GlobalTheory.T.balanced_nonneg_form_in_psd_cone O bar hCM (R k))
  choose C hC using hC
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    iSup_le fun hq => iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hli =>
      iSup_le fun hpr => ?_
  obtain ⟨k, ⟨e⟩⟩ := hcls X hq
  haveI := (hR k).1
  obtain ⟨h', hli', hpr', heq⟩ := GlobalTheory.PolFan.MultBound.transport e.symm h hli hpr
  have hle := (hC k m _ h' hli' hpr').trans (Finset.le_sup (f := C) (Finset.mem_univ k))
  rw [← heq]
  exact_mod_cast hle

end GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite
end
end

