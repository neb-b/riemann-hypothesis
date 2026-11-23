module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
public import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive
public import Formalism.LocalToGlobal.GroupLattices.FockModels.MkP

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

theorem dualInclusionLattices : DualHeightInclusion := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r lam0 hd e he
  exact ⟨lb_H_le_Re (mkG h m r lam0 hd) (0 : Fin 1) (lb_edgeLat_of_basis _ _ (restEdgeBasis _ _)) e he,
    lb_Hdual_le_Re' (mkG h m r lam0 hd) (0 : Fin 1) (lb_edgeLat_of_basis _ _ (restEdgeBasis _ _)) e he⟩

theorem hlSpans : HLSpans := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m lam0 hd L hL
  classical
  have h0 : ∃ (I : Type) (_ : Finite I) (b0 : Module.Basis I Kf (Vsp Kf lam0)),
      HL (O := O) ι σ lam0 L = Submodule.span O (Set.range b0) :=
    jm_HL_basis (mkG h m 0 lam0 hd) (0 : Fin 1) L hL
  obtain ⟨I, hI, x, hx⟩ := h0
  cases nonempty_fintype I
  have hcard : Fintype.card I = dimV Kf lam0 := (Module.finrank_eq_card_basis x).symm
  refine ⟨x.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [hx]
  congr 1
  simp

theorem mem_span_of_coord {O Kf V : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {I : Type} [Finite I] (x : Module.Basis I Kf V) (a : I → Kf)
    (ha : ∀ i, a i ≠ 0) (F : V) (hF : ∀ i, (a i)⁻¹ * x.coord i F ∈ Set.range (algebraMap O Kf)) :
    F ∈ Submodule.span O (Set.range fun i => a i • x i) := by
  haveI := Fintype.ofFinite I
  rw [← x.sum_repr F]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨o, ho⟩ := hF i
  have e : x.repr F i • x i = o • (a i • x i) := by
    rw [← algebraMap_smul Kf o (a i • x i), ho, smul_smul, Module.Basis.coord_apply]
    congr 1
    field_simp [ha i]
  rw [e]
  exact Submodule.smul_mem _ o (Submodule.subset_span ⟨i, rfl⟩)

theorem bePerfect : BePerfect := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r lam0 hd e he
  have hw := w_ne h
  have hp := p_eq h
  set c : Kf := algebraMap O Kf w with hc
  set A : ℤ := Ar r lam0 with hA
  have hpA : (p : Kf) ^ A * c ^ (-A) = c ^ A := by
    rw [hp, ← zpow_natCast c 2, ← zpow_mul, ← zpow_add₀ hw]
    congr 1
    push_cast
    ring
  have first : ∀ G, G ∈ Re' p ι σ w r lam0 e ↔
      ∀ F ∈ Re p ι σ w r lam0 e, be p r lam0 F G ∈ Set.range (algebraMap O Kf) := by
    intro G
    constructor
    · rintro ⟨ψ, hψ, rfl⟩ F ⟨z, hz, rfl⟩
      have e2 : be p r lam0 ((LinearMap.restrictScalars O ((LinearMap.lsmul Kf _) (c ^ (-A)))) z)
          ((LinearMap.restrictScalars O ((LinearMap.lsmul Kf _) (c ^ (-A)))) ψ) = ψ z := by
        show (c ^ (-A) • ψ) (((p : Kf) ^ A) • (c ^ (-A) • z)) = ψ z
        rw [LinearMap.smul_apply, map_smul, map_smul, smul_smul, smul_smul, mul_assoc, hpA,
          ← zpow_add₀ hw, neg_add_cancel, zpow_zero, one_smul]
      rw [e2]
      exact hψ z hz
    · intro hG
      refine ⟨c ^ A • G, ?_, ?_⟩
      · intro z hz
        have h1 := hG (c ^ (-A) • z) ⟨z, hz, rfl⟩
        have e2 : be p r lam0 (c ^ (-A) • z) G = (c ^ A • G) z := by
          show G (((p : Kf) ^ A) • (c ^ (-A) • z)) = (c ^ A • G) z
          rw [smul_smul, hpA, map_smul, LinearMap.smul_apply]
        rw [← e2]
        exact h1
      · show c ^ (-A) • (c ^ A • G) = G
        rw [smul_smul, ← zpow_add₀ hw, neg_add_cancel, zpow_zero, one_smul]
  refine ⟨first, fun F => ⟨fun hF G hG => (first G).1 hG F hF, fun hF => ?_⟩⟩
  obtain ⟨I, hI, x, π, -, -, -, -, c5, c6⟩ := elementary_divisor_basis h m r lam0 hd e he
  rw [← c5]
  apply mem_span_of_coord x _ (fun i => zpow_ne_zero _ hw)
  intro i
  have h1 := hF ((c ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i)
    (by rw [← c6]; exact Submodule.subset_span ⟨i, rfl⟩)
  have e2 : be p r lam0 F ((c ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i) =
      (c ^ (-order r lam0 (π i)))⁻¹ * x.coord i F := by
    show ((c ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i) (((p : Kf) ^ A) • F) = _
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    congr 1
    rw [hp, ← zpow_natCast c 2, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_neg]
    congr 1
    unfold order
    push_cast
    ring
  rw [← e2]
  exact h1

end Formalism.L2.G.Model
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.FockModels.MulMemRiemannRochSpaceAdd
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem dualWeyl_mul (R : Type*) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ)
    {f g : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (hg : g ∈ dualWeyl R r n ν') :
    f * g ∈ dualWeyl R r n (ν + ν') := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

theorem nablaL_mul (R K : Type*) [CommRing R] [Field K] [Algebra R K] (k n : ℕ) (ν ν' : Fin n → ℕ)
    (g : Matrix (Fin k) (Fin k) K) {F G : MvPolynomial (Fin k × Fin n) K}
    (hF : F ∈ nablaL R K k n ν g) (hG : G ∈ nablaL R K k n ν' g) : F * G ∈ nablaL R K k n (ν + ν') g := by
  simp only [nablaL, Submodule.mem_comap, Submodule.mem_map, LinearMap.coe_restrictScalars,
    AlgHom.toLinearMap_apply] at hF hG ⊢
  obtain ⟨f, hf, hfF⟩ := hF
  obtain ⟨f', hf', hfG⟩ := hG
  exact ⟨f * f', dualWeyl_mul R k n ν ν' hf hf', by rw [map_mul, map_mul, hfF, hfG]⟩

theorem toNat_add_last {m : ℕ} (lam mu : Fin (m + 1) → ℤ) (hl : Antitone lam) (hm : Antitone mu) :
    (fun t => ((lam + mu) t - (lam + mu) (Fin.last m)).toNat) =
      (fun t => (lam t - lam (Fin.last m)).toNat) + fun t => (mu t - mu (Fin.last m)).toNat := by
  funext t
  have h1 := hl (Fin.le_last t)
  have h2 := hm (Fin.le_last t)
  simp only [Pi.add_apply]
  omega

theorem nablaLTw_mul (R K : Type*) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam mu : Fin (m + 1) → ℤ)
    (hl : Antitone lam) (hm : Antitone mu) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det)
    {F G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K}
    (hF : F ∈ nablaLTw R K m lam g) (hG : G ∈ nablaLTw R K m mu g) : F * G ∈ nablaLTw R K m (lam + mu) g := by
  simp only [nablaLTw, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply] at hF hG ⊢
  obtain ⟨F0, hF0, rfl⟩ := hF
  obtain ⟨G0, hG0, rfl⟩ := hG
  have hd : g.det ≠ 0 := hg.ne_zero
  refine ⟨F0 * G0, ?_, ?_⟩
  · rw [toNat_add_last lam mu hl hm]
    exact nablaL_mul R K (m + 1) (m + 1) _ _ g hF0 hG0
  · rw [smul_mul_smul_comm, ← zpow_add₀ hd, Pi.add_apply, neg_add]

theorem mul_mem_riemannRochSpace_add (O Kf : Type*) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam mu : Fin (m + 1) → ℤ)
    (hl : Antitone lam) (hm : Antitone mu) (Λ : Submodule O (Fin (m + 1) → Kf))
    {F G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf}
    (hF : F ∈ H0 O m lam Λ) (hG : G ∈ H0 O m mu Λ) : F * G ∈ H0 O m (lam + mu) Λ := by
  have hlm : Antitone (lam + mu) := hl.add hm
  unfold H0 at hF hG ⊢
  rw [if_pos hl] at hF
  rw [if_pos hm] at hG
  rw [if_pos hlm]
  simp only [Submodule.mem_iInf] at hF hG ⊢
  intro g hg
  exact nablaLTw_mul O Kf m lam mu hl hm g hg.1 (hF g hg) (hG g hg)

theorem tensorLat_mul (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}
    (M M' M'' : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ F ∈ M s, ∀ G ∈ M' s, F * G ∈ M'' s) :
    ∀ P ∈ tensorLat R K M, ∀ Q ∈ tensorLat R K M', P * Q ∈ tensorLat R K M'' := by
  intro P hP Q hQ
  have hPQ : P * Q ∈ tensorLat R K M * tensorLat R K M' := Submodule.mul_mem_mul hP hQ
  unfold tensorLat at hPQ ⊢
  rw [Submodule.span_mul_span] at hPQ
  refine Submodule.span_mono ?_ hPQ
  rintro _ ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩
  exact ⟨fun s => F s * G s, fun s => h s _ (hF s) _ (hG s), by simp only [map_mul, Finset.prod_mul_distrib]⟩

theorem lamAt_add {n' m : ℕ} (lam0 mu0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (lam0 + mu0) s = lamAt lam0 s + lamAt mu0 s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.add_apply]
    ring

private lemma lamAt_antitone_lemma {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (h : IsDominant lam0)
    (s : Fin n') : Antitone (lamAt lam0 s) := by
  unfold lamAt
  split_ifs
  · exact h s
  · intro i j hij
    have hr : j.rev ≤ i.rev := by
      rw [Fin.le_def] at hij ⊢
      simp only [Fin.val_rev]
      omega
    exact neg_le_neg (h s hr)

theorem products_sections_integral (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.tableLineDegreeFive.LevelPrimesProviso D := by
  unfold Formalism.MainNotions.tableLineDegreeFive.LevelPrimesProviso
  intro O Kf _ _ _ n' m lam0 mu0 Λ hl hm F hF G hG
  unfold Hten at hF hG ⊢
  refine tensorLat_mul O Kf _ _ _ ?_ F hF G hG
  intro s F' hF' G' hG'
  show F' * G' ∈ H0 O m (lamAt (lam0 + mu0) s) (Λ s)
  rw [lamAt_add]
  exact mul_mem_riemannRochSpace_add O Kf m _ _ (lamAt_antitone_lemma lam0 hl s) (lamAt_antitone_lemma mu0 hm s) (Λ s) hF' hG'

end Formalism.L2.G.Model
end
end

