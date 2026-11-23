module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteHermitianIsometricOfSameBadPrimes
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermFramePairNormalFormMovedByIsometry
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassClassEqWeightCount
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FewOrbitsSubspacesHermitianLatticeDiscriminant
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.Mass.FewOrbits

theorem mem_iff_prod_le {R : Type*} [CommRing R] {A : Set (Ideal R)} (hA : A.Finite)
    (hm : ∀ P ∈ A, P.IsMaximal) (P : Ideal R) : P ∈ A ↔ P.IsMaximal ∧ ∏ᶠ Q ∈ A, Q ≤ P := by
  rw [finprod_mem_eq_finite_toFinset_prod _ hA]
  constructor
  · intro hP
    exact ⟨hm P hP, Ideal.prod_le_inf.trans (Finset.inf_le (hA.mem_toFinset.2 hP))⟩
  · rintro ⟨hPm, hle⟩
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.IsPrime.prod_le hPm.isPrime).1 hle
    have hQm := hm Q (hA.mem_toFinset.1 hQ)
    exact (hQm.eq_of_le hPm.ne_top hQP) ▸ hA.mem_toFinset.1 hQ

theorem nondeg {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x : V, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have := hp τ x hne
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (j n : ℕ), 1 ≤ n → ∃ s : Finset (Submodule K V), (s.card : ℝ) ≤ (n : ℝ) ^ (1 + Real.logb 2 (Module.finrank ℚ K)) ∧ (∀ U ∈ s, Module.finrank K U = j) ∧ ∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) n).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp hO j n hn
  have hW := _root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hp
  have hmaxOf : ∀ (U : Submodule K V) (M : Submodule (𝓞 K) U), ∀ P ∈ badP (hRes h U) M, P.IsMaximal := by
    intro U M P hP
    unfold badP at hP
    exact hP.1
  obtain ⟨Q, hQ⟩ : ∃ Q : Submodule K V → Ideal (𝓞 K) → Prop, ∀ U I, Q U I ↔
      (Module.finrank K U = j ∧ ∃ M : Submodule (𝓞 K) U, IsMaxLat (hRes h U) M ∧
        ∏ᶠ P ∈ badP (hRes h U) M, P = I) := ⟨_, fun _ _ => Iff.rfl⟩
  have hpick : ∀ I : Ideal (𝓞 K), ∃ U₀ : Submodule K V, (∃ U, Q U I) → Q U₀ I := by
    intro I
    by_cases hI : ∃ U, Q U I
    · obtain ⟨U, hU⟩ := hI
      exact ⟨U, fun _ => hU⟩
    · exact ⟨⊥, fun h' => absurd h' hI⟩
  choose pick hpickQ using hpick
  obtain ⟨hfin, hcard⟩ := Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K (n : ℝ) (by exact_mod_cast hn)
  refine ⟨(hfin.toFinset.filter (fun I => ∃ U, Q U I)).image pick, ?_, ?_, ?_⟩
  · calc _ ≤ (hfin.toFinset.card : ℝ) := by
          exact_mod_cast Finset.card_image_le.trans (Finset.card_filter_le _ _)
      _ = _ := by rw [Set.ncard_eq_toFinset_card _ hfin]
      _ ≤ _ := hcard
  · intro U hU
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hU
    exact ((hQ _ _).1 (hpickQ I (Finset.mem_filter.1 hI).2)).1
  · intro U hUj hne
    obtain ⟨L, hL⟩ := hne
    unfold latsDisc at hL
    obtain ⟨hLi, hLd⟩ := hL
    obtain ⟨-, hsU, hpU, -⟩ := hW.2 U
    have hnU := nondeg (hRes h U) hpU
    obtain ⟨M, hM, hLM⟩ := (GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K U (hRes h U) hK hsU hnU).1 L hLi
    have hd := (GlobalTheory.Mass.DiscOrder.main K U (hRes h U) hK hsU hnU L hLi).2.2.1 M hM.1 hLM
    obtain ⟨hbf, hdisc, -, -⟩ := GlobalTheory.MaxLatStruct.main K U (hRes h U) hK hsU hnU M hM
    obtain ⟨I, hIdef⟩ : ∃ I, ∏ᶠ P ∈ badP (hRes h U) M, P = I := ⟨_, rfl⟩
    have hnorm : Ideal.absNorm I = discN (hRes h U) M := by
      rw [hdisc, ← hIdef, finprod_mem_eq_finite_toFinset_prod _ hbf,
        finprod_mem_eq_finite_toFinset_prod _ hbf, map_prod]
    have hdv : Ideal.absNorm I ∣ n := ⟨idxN M L ^ 2, by rw [hnorm, ← hLd]; exact hd.2⟩
    have hpos : 0 < Ideal.absNorm I := Nat.pos_of_dvd_of_pos hdv hn
    have hID : I ∈ hfin.toFinset := by
      refine hfin.mem_toFinset.2 ⟨fun hb => by simp [hb] at hpos, ?_⟩
      exact_mod_cast Nat.le_of_dvd hn hdv
    have hex : ∃ U', Q U' I := ⟨U, (hQ U I).2 ⟨hUj, M, hM, hIdef⟩⟩
    obtain ⟨hj0, M₀, hM₀, hkey⟩ := (hQ _ _).1 (hpickQ I hex)
    obtain ⟨-, hs0, hp0, -⟩ := hW.2 (pick I)
    have hn0 := nondeg (hRes h (pick I)) hp0
    obtain ⟨hbf0, -, -, -⟩ := GlobalTheory.MaxLatStruct.main K (pick I) (hRes h (pick I)) hK hs0 hn0 M₀ hM₀
    have hbeq : badP (hRes h (pick I)) M₀ = badP (hRes h U) M := by
      ext P
      rw [mem_iff_prod_le hbf0 (hmaxOf _ _) P, mem_iff_prod_le hbf (hmaxOf _ _) P, hkey, hIdef]
    obtain ⟨e, he⟩ := _root_.GlobalTheory.Mass.SameBad.main K (pick I) (hRes h (pick I)) hK hs0 hp0 hO (↥U) (hRes h U) hsU hpU
      (by rw [hj0, hUj]) M₀ M hM₀ hM hbeq
    obtain ⟨g, hg, hgx⟩ := hW.1 (pick I) U e (fun x y => he x y)
    refine ⟨pick I, Finset.mem_image.2 ⟨I, Finset.mem_filter.2 ⟨hID, hex⟩, rfl⟩, ⟨g, hg⟩, ?_⟩
    ext y
    change y ∈ Formalism.HermitianLatticesTheory.gmap g (pick I) ↔ y ∈ U
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hgx ⟨x, hx⟩
      change g x ∈ U
      rw [this]
      exact (e ⟨x, hx⟩).2
    · intro hy
      refine ⟨(e.symm ⟨y, hy⟩ : V), (e.symm ⟨y, hy⟩).2, ?_⟩
      change g _ = y
      rw [hgx (e.symm ⟨y, hy⟩)]
      simp

end GlobalTheory.Mass.FewOrbits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrEqvEquivalence
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.FrameEqv
open AdaptInv
section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem map_xa {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (k : ℕ) {x : V} (hx : x ∈ G.Xa k) : n x ∈ G'.Xa k := by
  have key : G.Xa k ≤ (G'.Xa k).comap (n : V →ₗ[K] V) := by
    show Submodule.span K _ ≤ _
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b.val < k := hb
    have h1 : n (G.e b.castSucc) - G'.e b.castSucc ∈ G'.Xa b.val := h b.castSucc
    have h2 : n (G.e b.castSucc) =
        (n (G.e b.castSucc) - G'.e b.castSucc) + G'.e b.castSucc := by abel
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [h2]
    exact (G'.Xa k).add_mem (xa_mono G' hb'.le h1) (e_mem_xa G' b hb')
  exact key hx

theorem symm_xa {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (k : ℕ) : ∀ x ∈ G'.Xa k, n.symm x ∈ G.Xa k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx
    have key : G'.Xa k ≤ (G.Xa k).comap (n.symm : V →ₗ[K] V) := by
      show Submodule.span K _ ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val < k := hb
      have h1 : n (G.e b.castSucc) - G'.e b.castSucc ∈ G'.Xa b.val := h b.castSucc
      have h2 := ih b.val hb' _ h1
      have e1 : n.symm (G'.e b.castSucc) =
          G.e b.castSucc - n.symm (n (G.e b.castSucc) - G'.e b.castSucc) := by
        rw [map_sub, LinearEquiv.symm_apply_apply, sub_sub_cancel]
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
      rw [e1]
      exact (G.Xa k).sub_mem (e_mem_xa G b hb') (xa_mono G hb'.le h2)
    exact key hx

theorem symm_gr {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (a : Fin (r + 1)) : n.symm (G'.e a) - G.e a ∈ G.Xa a.val := by
  have h1 := symm_xa h a.val _ (h a)
  have e1 : n.symm (G'.e a) - G.e a = -(n.symm (n (G.e a) - G'.e a)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub]
  rw [e1]
  exact (G.Xa a.val).neg_mem h1

theorem inN_gr {F : FlagD H r} {n : V ≃ₗ[K] V} (h : F.InN (n : V →ₗ[K] V)) (a : Fin (r + 1)) :
    n (F.e a) - F.e a ∈ F.Xa a.val := by
  induction a using Fin.lastCases with
  | last =>
    rw [Fin.val_last]
    exact h.2.2.2 _ F.zperp
  | cast b =>
    rw [Fin.coe_castSucc]
    exact h.2.2.1 b

theorem gr_comp {G G' M : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (hM : SameGr G M) (a : Fin (r + 1)) : n (M.e a) - G'.e a ∈ G'.Xa a.val := by
  have e1 : n (M.e a) - G'.e a = n (M.e a - G.e a) + (n (G.e a) - G'.e a) := by
    rw [map_sub]; abel
  rw [e1]
  exact (G'.Xa a.val).add_mem (map_xa h a.val (hM a)) (h a)
end

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem frEqv_equivalence (F : FlagD H r) (Λ : Submodule (𝓞 K) V) : Equivalence (FrEqv F Λ) := by
  refine ⟨fun G => ⟨1, GlobalTheory.UnipStab.inN_one, one_smul _ _, fun a => by simp⟩, ?_, ?_⟩
  · rintro G G' ⟨n, hn, hΛ, hG⟩
    refine ⟨n⁻¹, GlobalTheory.UnipStab.inN_inv hn, ?_, fun a => symm_gr hG a⟩
    conv_lhs => rw [← hΛ]
    exact inv_smul_smul n Λ
  · rintro G G' G'' ⟨n, hn, hΛ, hG⟩ ⟨m, hm, hΛ', hG'⟩
    refine ⟨m * n, GlobalTheory.UnipStab.inN_mul hm hn, by rw [mul_smul, hΛ, hΛ'], fun a => ?_⟩
    have e1 : (m * n) (G.e a) - G''.e a = m (n (G.e a) - G'.e a) + (m (G'.e a) - G''.e a) := by
      rw [LinearEquiv.mul_apply, map_sub]; abel
    rw [e1]
    exact (G''.Xa a.val).add_mem (map_xa hG' a.val (hG a)) (hG' a)

theorem move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G G' : FlagD H r} {𝔡 : Ideal (𝓞 K)} {Λ : Submodule (𝓞 K) V}
    (h : FrEqv F Λ G G') (N : NF H r) (hN : Adapt F G 𝔡 N) :
    ∃ N' : NF H r, Adapt F G' 𝔡 N' ∧ N'.om Λ = N.om Λ ∧
      ∀ g : ℕ, (N'.IsTerm g Λ ↔ N.IsTerm g Λ) ∧ N'.gI g Λ = N.gI g Λ := by
  obtain ⟨n, hn, hΛ, hG⟩ := h
  have hiso : n ∈ isomGrp H := (mem_isomGrp H n).2 fun x y => hn.1 x y
  obtain ⟨N', he, -, -, -, hd, -, hrest⟩ := _root_.GlobalTheory.DegMove.exists_moved K V H hK r N n hiso
  refine ⟨N', ⟨hd.trans hN.1, fun a => ?_, fun a => ?_⟩, ?_, fun g => ?_⟩
  · rw [(he a).1]
    have e1 : n (N.F.e a) - F.e a = n (N.F.e a - F.e a) + (n (F.e a) - F.e a) := by
      rw [map_sub]; abel
    rw [e1]
    exact (F.Xa a.val).add_mem (GlobalTheory.UnipStab.map_Xa hn a.val (hN.2.1 a)) (inN_gr hn a)
  · rw [(he a).2]
    exact gr_comp hG hN.2.2 a
  · have h1 := (hrest 0 Λ).1
    rwa [hΛ] at h1
  · have h1 := hrest g Λ
    rw [hΛ] at h1
    exact ⟨h1.2.1, h1.2.2⟩

end GlobalTheory.DegAsm.FrameEqv

namespace GlobalTheory.DegAsm
open FrameEqv

theorem frEqv_invariants : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V), Equivalence (FrEqv F Λ) ∧ ∀ G G' : FlagD H r, FrEqv F Λ G G' → omI F G 𝔡 Λ = omI F G' 𝔡 Λ ∧ ∀ N : NF H r, Adapt F G 𝔡 N → ∃ N' : NF H r, Adapt F G' 𝔡 N' ∧ N'.om Λ = N.om Λ ∧ ∀ g : ℕ, (N'.IsTerm g Λ ↔ N.IsTerm g Λ) ∧ N'.gI g Λ = N.gI g Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r F 𝔡 Λ
  refine ⟨frEqv_equivalence F Λ, fun G G' h => ⟨?_, fun N hN => move hK h N hN⟩⟩
  have sub : ∀ {G G' : FlagD H r}, FrEqv F Λ G G' →
      (fun N : NF H r => N.om Λ) '' {N | Adapt F G 𝔡 N} ⊆
        (fun N : NF H r => N.om Λ) '' {N | Adapt F G' 𝔡 N} := by
    intro G G' h x hx
    obtain ⟨N, hN, rfl⟩ := hx
    obtain ⟨N', hN', hom, -⟩ := move hK h N hN
    exact ⟨N', hN', hom⟩
  unfold omI
  rw [Set.Subset.antisymm (sub h) (sub ((frEqv_equivalence F Λ).symm h))]

end GlobalTheory.DegAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairExistsUnipotentSplitLattice
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.SplitLift

section Lattice

variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (M : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

theorem exists_split (Λ : Submodule R V) (hfg : Λ.FG) (hsp : Submodule.span K (Λ : Set V) = ⊤)
    (S I : Submodule K V) :
    ∃ W : Submodule K V, W ≤ S ∧ W ⊓ I = ⊥ ∧ S ≤ W ⊔ I ∧
      ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ W ∧ l - w ∈ I := by
  set M : Submodule R V := Λ ⊓ S.restrictScalars R with hM
  have hMfg : M.FG := by
    have : Module.Finite R Λ := Module.Finite.iff_fg.2 hfg
    exact (Module.Finite.iff_fg (N := M)).1
      (Module.Finite.of_injective (Submodule.inclusion (inf_le_left : M ≤ Λ))
        (Submodule.inclusion_injective _))
  have : Module.Finite R M := Module.Finite.iff_fg.2 hMfg
  let π : M →ₗ[R] (V ⧸ I) := (I.mkQ.restrictScalars R) ∘ₗ M.subtype
  have : Module.IsTorsionFree R (V ⧸ I) := Module.IsTorsionFree.trans K
  have : Module.Finite R (LinearMap.range π) := inferInstance
  have : Module.Flat R (LinearMap.range π) := inferInstance
  have : Module.FinitePresentation R (LinearMap.range π) :=
    Module.finitePresentation_of_finite R _
  have : Module.Projective R (LinearMap.range π) := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π.rangeRestrict LinearMap.id
    π.surjective_rangeRestrict
  have hσ' : ∀ y, π (σ y) = (y : V ⧸ I) := fun y => by
    have := congrArg Subtype.val (LinearMap.congr_fun hσ y)
    simpa using this
  set N : Submodule R V := LinearMap.range (M.subtype ∘ₗ σ) with hN
  have key : ∀ l ∈ Λ, l ∈ S → ∃ w ∈ Λ, w ∈ Submodule.span K (N : Set V) ∧ l - w ∈ I := by
    intro l hl hlS
    let y : LinearMap.range π := ⟨π ⟨l, hl, hlS⟩, _, rfl⟩
    refine ⟨(σ y : V), (σ y).2.1, Submodule.subset_span ⟨y, rfl⟩, ?_⟩
    rw [← Submodule.Quotient.eq]
    exact (hσ' y).symm
  have hinj : ∀ d : R, d ≠ 0 → algebraMap R K d ≠ 0 := fun d hd =>
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd
  refine ⟨Submodule.span K (N : Set V), ?_, ?_, ?_, key⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact (σ y).2.2
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxI⟩
    obtain ⟨d, hd, y, hy⟩ := exists_smul_mem N hx
    have hy' : ((σ y : M) : V) = d • x := hy
    have h0 : (y : V ⧸ I) = 0 := by
      rw [← hσ' y]
      show I.mkQ ((σ y : M) : V) = 0
      rw [hy', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.smul_of_tower_mem d hxI
    have h1 : y = 0 := Subtype.ext h0
    rw [h1, map_zero, ← algebraMap_smul K d x] at hy'
    exact (smul_eq_zero.1 hy'.symm).resolve_left (hinj d hd)
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem (K := K) Λ (x := x) (by rw [hsp]; trivial)
    obtain ⟨w, -, hw, hwI⟩ := key _ hdx (S.smul_of_tower_mem d hx)
    have h1 : d • x ∈ Submodule.span K (N : Set V) ⊔ I :=
      Submodule.mem_sup.2 ⟨w, hw, _, hwI, by abel⟩
    rw [← algebraMap_smul K d x] at h1
    exact (Submodule.smul_mem_iff _ (hinj d hd)).1 h1

end Lattice

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

section Geometry
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem flip_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem mem_wSp_iff (F F' : FlagD H r) (w : V) : w ∈ wSp F F' ↔ ∀ y ∈ V0 F F', H.B y w = 0 := by
  rw [wSp, mem_perp_iff]
  exact ⟨fun h y hy => flip_zero (h y hy), fun h y hy => flip_zero (h y hy)⟩

theorem hermFlagPair_isotropic_sup_le_commonSpace (F F' : FlagD H r) : F.X ⊔ F'.X ≤ V0 F F' := le_sup_left

theorem isotropicMeet_le_jointSpan (F F' : FlagD H r) : II F F' ≤ V0 F F' :=
  (inf_le_left.trans le_sup_left).trans (hermFlagPair_isotropic_sup_le_commonSpace F F')

theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast b =>
    exact hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))

theorem X_perp (F : FlagD H r) {w x : V} (hw : ∀ a : Fin (r + 1), H.B (F.e a) w = 0) (hx : x ∈ F.X) :
    H.B x w = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip w) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    exact hw _
  exact this hx

theorem aniso_right {F F' : FlagD H r} {j : ℕ} {hj : j ≤ r} {c : K} (h : NFFull F F' j hj c)
    (hF : F.Aniso) : F'.Aniso := by
  obtain ⟨-, -, -, -, -, h6, -, -, h9⟩ := h
  intro w hw hww
  obtain ⟨x, hx, hwx⟩ := h9 w hw
  have h1 : H.B (w - x) (w - x) = 0 := by
    have a1 : H.B x (w - x) = 0 := hwx x (hermFlagPair_isotropic_sup_le_commonSpace F F' (Submodule.mem_sup_right hx))
    have a2 : H.B w x = 0 := flip_zero (X_perp F' hw hx)
    rw [map_sub H.B, LinearMap.sub_apply, a1, map_sub, hww, a2]
    simp
  have h2 : w - x ∈ F.X := hF _ (fun a => hwx _ (flag_vector_mem_base_lattice F F' a)) h1
  have h3 : w - x ∈ F'.X := ((h6 _ h2).1 hwx).2
  simpa using add_mem h3 hx

end Geometry

theorem latTh_eq (F F' : FlagD H r) (hI : II F F' ≤ wSp F F') (Λ : Submodule (𝓞 K) V) :
    latTh F F' Λ = (Λ ⊓ rs (𝓞 K) (wSp F F')) ⊔ rs (𝓞 K) (II F F') := by
  have hu : ∀ y ∈ wSp F F', y ∈ uPerp F F' := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hermFlagPair_isotropic_sup_le_commonSpace F F' hx)
  have hp : ∀ y ∈ wSp F F', y ∈ perp H (II F F') := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (isotropicMeet_le_jointSpan F F' hx)
  apply le_antisymm
  · rintro y ⟨⟨hy1, -⟩, hy3⟩
    obtain ⟨l, ⟨hl, -⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hy1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, x, hx, rfl⟩
    have : l + x - x ∈ wSp F F' := sub_mem hy3 (hI hx)
    simpa using this
  · refine sup_le ?_ ?_
    · rintro l ⟨hl, hw⟩
      exact ⟨⟨Submodule.mem_sup_left ⟨hl, hp l hw⟩, hu l hw⟩, hw⟩
    · intro x hx
      exact ⟨⟨Submodule.mem_sup_right hx, hu x (hI hx)⟩, hI hx⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ s ∈ N.R, N.Split (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hΛ
  obtain ⟨hfull, hlift, -, -, -, -, hw, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hL := (isLatMod_top_bot_iff Λ).1 hΛ.1.1.1
  obtain ⟨W, hWS, hWI, hSW, hWΛ⟩ :=
    exists_split Λ hL.1 hΛ.1.1.1.2 (wSp N.F N.F') (II N.F N.F')
  have hW : IsLift N.F N.F' W :=
    ⟨fun w h => (mem_wSp_iff _ _ w).1 (hWS h), hWI, fun w h => hSW ((mem_wSp_iff _ _ w).2 h)⟩
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hA : N.F.Aniso := by
    intro w h1 h2
    by_contra hne
    have := N.posdef σ w h1 hne
    rw [h2] at this
    simp at this
  obtain ⟨f, hf, hf', hfix, hmap⟩ := Formalism.HermitianLatticeCounting.P.complementLiftTransitive K V H r N.F N.F' W N.Wt
    ⟨1, by rw [star_one]; norm_num⟩ hA (aniso_right hfull hA) hW hlift
  let s : V ≃ₗ[K] V := LinearEquiv.ofBijective f hf.2.1
  refine ⟨s, Subgroup.subset_closure ⟨hf, hf'⟩, ?_⟩
  have hI : II N.F N.F' ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_right
  have hWt : N.Wt ≤ wSp N.F N.F' := by rw [hw]; exact le_sup_left
  rw [NF.Split, latTh_eq _ _ hI]
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rintro y ⟨hy, hyw⟩
    obtain ⟨l, hl, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy
    have hlw : l ∈ wSp N.F N.F' := by
      refine (mem_wSp_iff _ _ l).2 fun y hy => ?_
      rw [← hf.1, hfix y hy]
      exact (mem_wSp_iff _ _ _).1 hyw y hy
    obtain ⟨w, hw1, hw2, hw3⟩ := hWΛ l hl hlw
    refine Submodule.mem_sup.2 ⟨f w, ⟨Submodule.smul_mem_pointwise_smul w s Λ hw1, ?_⟩, l - w, hw3, ?_⟩
    · show f w ∈ N.Wt
      rw [← hmap]
      exact ⟨w, hw2, rfl⟩
    · show f w + (l - w) = f l
      rw [← hfix _ (isotropicMeet_le_jointSpan _ _ hw3), map_sub]
      abel
  · exact sup_le_sup_right (inf_le_inf_left _ fun x hx => hWt hx) _

end GlobalTheory.DegCnt.SplitLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassClassEqWeightCountStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_class_eq_weight_count_alt : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat f f' ∈ c1 → (∃ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t ∧ H.Zhat t.f t.f' ∈ c1) → ∃ w : ℝ, 0 < w ∧ w ≤ P.Hp ^ (3 * (r + 1) ^ 2) ∧ (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) = ENNReal.ofReal w * ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (({Λ | LocNG.IsTermOver P d.1 (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} : Set (Submodule M.L.O V)).encard : ℝ≥0∞) := by
  first | exact @GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count | exact GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count | (intros; apply GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count <;> assumption)
end

