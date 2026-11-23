module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0343
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalSectionsCompatibleSystem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBundleRootFromRelations
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.EisTerm

theorem flat_norm_le_height_rpow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (K : Subgroup (G2 σ Y))
    (a : G2 σ Y → ℝ) (hK : IsCompact (K : Set (G2 σ Y))) (hH : IsHgt K a) (ha : ∀ x, 0 < a x)
    (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ C : ℝ, ∀ (s : ℂ) (x : G2 σ Y), ‖flat a f s₁ s x‖ ≤ C * a x ^ (s.re + (n : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun s x => ?_⟩
  obtain ⟨p, t, hp, k, hk, rfl⟩ := hH.iwa x
  have hpos := ha (p * k)
  have hval := hH.val p t hp k hk
  have hlaw := hf.law p t k hp
  have hfk : ‖f (p * k)‖ = a (p * k) ^ (s₁.re + (n : ℝ) / 2) * ‖f k‖ := by
    have h1 : ‖(χ (Matrix.GeneralLinearGroup.det t) : ℂ)‖ = 1 := by
      first
        | exact Circle.norm_coe _
        | exact Circle.abs_coe _
        | simp
        | exact mem_sphere_zero_iff_norm.mp (χ (Matrix.GeneralLinearGroup.det t)).2
    rw [hlaw, ← hval, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, h1, one_mul]
    congr 2
    simp
  have e1 : a (p * k) ^ (s.re + (n : ℝ) / 2) =
      a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2) := by
    rw [← Real.rpow_add hpos]
    congr 1
    rw [Complex.sub_re]
    ring
  show ‖((a (p * k) : ℝ) : ℂ) ^ (s - s₁) * f (p * k)‖ ≤ _
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hfk, e1]
  have h0 : 0 ≤ a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hpos.le _) (Real.rpow_nonneg hpos.le _)
  calc a (p * k) ^ ((s - s₁).re) * (a (p * k) ^ (s₁.re + (n : ℝ) / 2) * ‖f k‖)
      = (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) * ‖f k‖ := by ring
    _ ≤ (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) * C :=
      mul_le_mul_of_nonneg_left (hC k hk) h0
    _ = C * (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) := by ring

end GlobalTheory.CompanionTheory.EisTerm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalAlgebraisationSchemes
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
open GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem exists_compatible {R : Type} [CommRing R] (I : Ideal R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {N : ∀ e, LB (Y e).left}
    {v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))} {D : ℤ}
    (step : ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D),
      SecMaps (pullPow (v e) D) σ (secPull σ' (β e)))
    {τ : Type} (a₀ : τ → LB.Sec (pw (N 0) D)) :
    ∃ a : ∀ e, τ → LB.Sec (pw (N e) D), a 0 = a₀ ∧
      ∀ e i, SecMaps (pullPow (v e) D) (a e i) (secPull (a (e + 1) i) (β e)) := by
  choose L hL using step
  exact ⟨fun e i => Nat.rec (motive := fun e => LB.Sec (pw (N e) D)) (a₀ i) (fun e x => L e x) e,
    rfl, fun e i => hL e _⟩

theorem tower_sections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (n p q : ℕ) (a : ∀ e, Fin (p + 1) → LB.Sec (pw (N e) (n : ℤ))) (c : ∀ e, Fin (q + 1) → LB.Sec (pw (N e) ((n : ℤ) + 1))), 1 ≤ n ∧ VeryAmpleBy (Y 0).hom (pw (N 0) (n : ℤ)) (a 0) ∧ VeryAmpleBy (Y 0).hom (pw (N 0) ((n : ℤ) + 1)) (c 0) ∧ (∀ e i, SecMaps (pullPow (v e) (n : ℤ)) (a e i) (secPull (a (e + 1) i) (β e))) ∧ (∀ e i, SecMaps (pullPow (v e) ((n : ℤ) + 1)) (c e i) (secPull (c (e + 1) i) (β e))) := by
  intro R _ _ I Y β hβ hP N v hN hA
  obtain ⟨d, hd, m₁, s, m₂, s', hs, hs'⟩ := _root_.GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple (R ⧸ I ^ (0 + 1)) (Y 0) (N 0) (hN 0).1 hA
  obtain ⟨t₁, ht₁⟩ := _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift R I Y β hβ hP N v hN d hd m₁ s hs
  obtain ⟨t₂, ht₂⟩ := _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift R I Y β hβ hP N v hN (d + 1) (by omega) m₂ s' hs'
  set k := max t₁ t₂ with hk
  set t := 1 + (d + 1) * k with ht
  set t' := 1 + d * k with ht'
  have hkt : k ≤ t := by nlinarith
  have hkt' : k ≤ t' := by nlinarith
  have h1 : t₁ ≤ t := (le_max_left _ _).trans hkt
  have h2 : t₂ ≤ t' := (le_max_right _ _).trans hkt'
  have e₁ : ((d * t : ℕ) : ℤ) = (d : ℤ) * (t : ℕ) := by push_cast; ring
  have e₂ : ((d * t : ℕ) : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) * (t' : ℕ) := by
    simp only [ht, ht']; push_cast; ring
  have hc₁ : 0 < Fintype.card (Fin t → Fin (m₁ + 1)) := Fintype.card_pos
  have hc₂ : 0 < Fintype.card (Fin t' → Fin (m₂ + 1)) := Fintype.card_pos
  obtain ⟨p, hp⟩ : ∃ p, Fintype.card (Fin t → Fin (m₁ + 1)) = p + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₁).symm⟩
  obtain ⟨q, hq⟩ : ∃ q, Fintype.card (Fin t' → Fin (m₂ + 1)) = q + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₂).symm⟩
  let E₁ : Fin (p + 1) ≃ (Fin t → Fin (m₁ + 1)) := (Fintype.equivFinOfCardEq hp).symm
  let E₂ : Fin (q + 1) ≃ (Fin t' → Fin (m₂ + 1)) := (Fintype.equivFinOfCardEq hq).symm
  have ht1 : 1 ≤ t := by omega
  have ht1' : 1 ≤ t' := by omega
  have va := _root_.GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono _ (Y 0).hom (N 0) _ _ t e₁.symm m₁ s (hN 0).1 ht1 hs p E₁
  have vc := _root_.GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono _ (Y 0).hom (N 0) _ _ t' e₂.symm m₂ s' (hN 0).1 ht1' hs' q E₂
  obtain ⟨a, ha0, ha⟩ := exists_compatible I (v := v) (ht₁ t h1 _ e₁) (fun j => secMono e₁.symm s (E₁ j))
  obtain ⟨c, hc0, hc⟩ := exists_compatible I (v := v) (ht₂ t' h2 _ e₂) (fun j => secMono e₂.symm s' (E₂ j))
  refine ⟨d * t, p, q, a, c, Nat.mul_pos hd ht1, ?_, ?_, ha, hc⟩
  · rw [ha0]; exact va
  · rw [hc0]; exact vc

theorem schemes_of_closedProj : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro hGE R _ _ I hI Y β hβ hP N hN hv hA
  choose v hvg using hv
  have hNv : ∀ e, (N e).IsLB ∧ (v e).IsGen := fun e => ⟨hN e, hvg e⟩
  obtain ⟨n, p, q, a, c, hn, ha0, hc0, hca, hcc⟩ := tower_sections R I Y β hβ hP N v hNv hA
  set D : ℤ := (n : ℤ) * ((n + 1 : ℕ) : ℤ) with hD
  have h1 : (n : ℤ) * ((n + 1 : ℕ) : ℤ) = D := rfl
  have h2 : ((n : ℤ) + 1) * ((n : ℕ) : ℤ) = D := by rw [hD]; push_cast; ring
  have hcard : ∀ (k r : ℕ), ∃ m, Fintype.card (Fin k → Fin (r + 1)) = m + 1 := fun k r =>
    ⟨_, (Nat.succ_pred_eq_of_pos (Fintype.card_pos (α := Fin k → Fin (r + 1)))).symm⟩
  obtain ⟨m₁, hm₁⟩ := hcard (n + 1) p
  obtain ⟨m₂, hm₂⟩ := hcard n q
  let E₁ : Fin (m₁ + 1) ≃ (Fin (n + 1) → Fin (p + 1)) := (Fintype.equivFinOfCardEq hm₁).symm
  let E₂ : Fin (m₂ + 1) ≃ (Fin n → Fin (q + 1)) := (Fintype.equivFinOfCardEq hm₂).symm
  let m := m₁ + 1 + m₂
  let E : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  let z : ∀ e, Fin (m + 1) → LB.Sec (pw (N e) D) := fun e j =>
    Sum.elim (fun i => secMono h1 (a e) (E₁ i)) (fun i => secMono h2 (c e) (E₂ i)) (E j)
  have hz1 : ∀ e w, z e (E.symm (Sum.inl (E₁.symm w))) = secMono h1 (a e) w := fun e w => by
    simp [z]
  have hz2 : ∀ e w, z e (E.symm (Sum.inr (E₂.symm w))) = secMono h2 (c e) w := fun e w => by
    simp [z]
  have hva : VeryAmpleBy (Y 0).hom (pw (N 0) D) (z 0) := by
    have x1 := _root_.GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono _ (Y 0).hom (N 0) _ _ (n + 1) h1 p (a 0) (hN 0) (by omega) ha0 m₁ E₁
    have x2 := _root_.GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono _ (Y 0).hom (N 0) _ _ n h2 q (c 0) (hN 0) hn hc0 m₂ E₂
    exact _root_.GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union _ (Y 0).hom _ (isLB_pw (hN 0) D) m₁ m₂ m _ _ E x1 x2
  have hzc : ∀ e j, SecMaps (pullPow (v e) D) (z e j) (secPull (z (e + 1) j) (β e)) := fun e j => by
    simp only [z]
    rcases E j with i | i
    · exact secMaps_secMono (v e) h1 (a e) (a (e + 1)) (hca e) _
    · exact secMaps_secMono (v e) h2 (c e) (c (e + 1)) (hcc e) _
  obtain ⟨X, Q, ζ, b, ω, hQ, hX, hXa, hb, hbc, hω, hωz, hquad, hcov⟩ :=
    _root_.GlobalTheory.CompanionTheory.FormalAlg.exists_tower_algebraisation hGE R I hI Y β hβ (fun e => pw (N e) D) (fun e => pullPow (v e) D)
      (fun e => ⟨isLB_pw (hN e) D, pullPow_isGen _ _ (hvg e)⟩) m z hzc hva
  let ia : (Fin (n + 1) → Fin (p + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inl (E₁.symm w))
  let ic : (Fin n → Fin (q + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inr (E₂.symm w))
  have hA' : ⨆ i : Fin (p + 1), nonzeroLocus (ζ (ia fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (p + 1) => ia fun _ => i) (by
      rw [iSup_range, ← ha0.1]
      refine iSup_congr fun i => ?_
      rw [hz1, nonzeroLocus_secMono_const h1 _ _ (by omega)])
    rwa [iSup_range] at this
  have hC' : ⨆ i : Fin (q + 1), nonzeroLocus (ζ (ic fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (q + 1) => ic fun _ => i) (by
      rw [iSup_range, ← hc0.1]
      refine iSup_congr fun i => ?_
      rw [hz2, nonzeroLocus_secMono_const h2 _ _ hn])
    rwa [iSup_range] at this
  obtain ⟨A, ωA, hAL, hωA, hAc⟩ := _root_.GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese X.left Q hQ (n + 1) (by omega) (Fin (p + 1)) (fun w => ζ (ia w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ia, hz1]; exact secMono_mul h1 (a e) w₁ w₂ w₃ w₄ hw c'') c') hA'
  obtain ⟨C, ωC, hCL, hωC, hCc⟩ := _root_.GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese X.left Q hQ n hn (Fin (q + 1)) (fun w => ζ (ic w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ic, hz2]; exact secMono_mul h2 (c e) w₁ w₂ w₃ w₄ hw c'') c') hC'
  refine ⟨X, tw C A (-1), b, hX, isLB_tw hCL hAL _,
    _root_.GlobalTheory.CompanionTheory.FormalAlg.relAmple_tw_of_roots R X Q m ζ hQ hXa A C n hn hAL hCL ⟨ωA, hωA⟩ ⟨ωC, hωC⟩, hb, hbc, fun e => ?_⟩
  refine _root_.GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw (b e) A C (N e) n hAL hCL (hN e) ?_ ?_
  · refine hAc _ (b e) (N e) n D h1 (a e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ia w)
    simp only [ia, hz1] at this
    exact this
  · refine hCc _ (b e) (N e) ((n : ℤ) + 1) D h2 (c e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ic w)
    simp only [ic, hz2] at this
    exact this

end GlobalTheory.CompanionTheory.FormalAlg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerFixesRootUnique
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.TameAction


open GlobalTheory.TameQuot GlobalTheory.WeilDeligne in
theorem eq_zero_of_fixes_primitiveRoot : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ ξ : Ω, IsPrimitiveRoot ξ (normV v ^ N - 1) → ∀ (a : ℕ) (t i : Dec (F := F) A), a < N → (i : G F Ω) ∈ Ine (F := F) A → ((φ ^ a * t ^ N * i : Dec (F := F) A) : G F Ω) ξ = ξ → a = 0 := by
  intro F Ω _ _ _ _ _ A v hA φ hφ N hN ξ hξ' a t i haN hi hfix
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hq := one_lt_normV v
  obtain ⟨n, hn⟩ : ∃ n, normV v ^ N = n + 1 :=
    ⟨_, (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm⟩
  have hn0 : n ≠ 0 := by
    have := one_lt_pow₀ hq hN.ne'
    omega
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn0⟩
  have hξ : IsPrimitiveRoot ξ n := by
    have e : normV v ^ N - 1 = n := by omega
    rwa [e] at hξ'
  have hnv : ¬ A.valuation (n : Ω) < 1 := by
    intro h
    have h1 : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]
      exact card_nsmul_eq_zero'
    have h2 : ((n : ℕ) : 𝓞 F) ∈ v.asIdeal := (hA _).1 (by simpa using h)
    have h3 := v.asIdeal.sub_mem (v.asIdeal.pow_mem_of_mem h1 N hN) h2
    rw [← Nat.cast_pow, hn] at h3
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))
  have hξ1 : A.valuation ξ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hn0 hξ.pow_eq_one).le
  let θ : Dec (F := F) A →* (ZMod n)ˣ := (hξ.autToPow F).comp (Dec (F := F) A).subtype
  have hθ : ∀ (g : Dec (F := F) A) (k : ℕ), (θ g : ZMod n) = k ↔ g.1 ξ = ξ ^ k := fun g k => by
    have hu : IsPrimitiveRoot (hξ.isUnit hn0).unit n :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hξ)
    rw [← hξ.autToPow_spec F g.1]
    change (θ g : ZMod n) = k ↔ ξ ^ (θ g : ZMod n).val = _
    conv_lhs => rw [← ZMod.natCast_zmod_val (θ g : ZMod n)]
    rw [ZMod.natCast_eq_natCast_iff]
    generalize (θ g : ZMod n).val = m
    conv_lhs => rw [hu.eq_orderOf, ← pow_eq_pow_iff_modEq, Units.ext_iff]
    simp
  have hθ' : ∀ (g : Dec (F := F) A) (k : ℕ), A.valuation (g.1 ξ - ξ ^ k) < 1 → (θ g : ZMod n) = k :=
    fun g k h => (hθ g k).2 (eq_of_pow_eq_one A hnv (by rw [← map_pow, hξ.pow_eq_one, map_one])
      (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]) h)
  have hI : ∀ σ : Dec (F := F) A, σ.1 ∈ Ine (F := F) A → θ σ = 1 := fun σ hσ =>
    Units.ext (by simpa using hθ' σ 1 (by simpa using hσ.2 ξ hξ1))
  have hF : (θ φ : ZMod n) = (normV v : ℕ) := hθ' φ _ (hφ.2 ξ hξ1)
  have ho : IsOpen (θ.ker : Set (Dec (F := F) A)) := by
    have e : (θ.ker : Set (Dec (F := F) A)) = Subtype.val ⁻¹' {σ : G F Ω | σ ξ = ξ} := by
      ext g
      have := hθ g 1
      rw [pow_one, Nat.cast_one] at this
      exact Units.ext_iff.trans this
    rw [e]
    exact (isOpen_setOf_apply (F := F) ξ (fun t => t = ξ)).preimage continuous_subtype_val
  have h3 : θ φ ^ N = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hF, ← Nat.cast_pow, hn]; simp)
  have hr : ∀ g, θ g ∈ Subgroup.zpowers (θ φ) := by
    have h4 : ⊤ ≤ (Subgroup.zpowers (θ φ)).comap θ := by
      rw [← closure_frob_sup_Ine F Ω A v hA φ hφ]
      refine Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2
        (Subgroup.mem_zpowers _)) fun σ hσ => ?_) (Subgroup.isClosed_of_isOpen _
          (Subgroup.isOpen_mono (fun σ hσ => ?_) ho))
      · rw [Subgroup.mem_comap, hI σ hσ]
        exact one_mem _
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hσ]
        exact one_mem _
    exact fun g => h4 (Subgroup.mem_top g)
  have ht : θ t ^ N = 1 := by
    obtain ⟨b, hb⟩ := hr t
    rw [← hb, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]
  have h5 : θ φ ^ a = 1 := by
    have h6 : θ (φ ^ a * t ^ N * i) = 1 :=
      Units.ext (by simpa using (hθ (φ ^ a * t ^ N * i) 1).2 (by simpa using hfix))
    rwa [map_mul, map_mul, map_pow, map_pow, ht, hI i hi, mul_one, mul_one] at h6
  have h1 : ((θ φ ^ a : (ZMod n)ˣ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    rw [Nat.cast_one]; exact congrArg Units.val h5
  rw [Units.val_pow_eq_pow_val, hF, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff] at h1
  have h2 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h1.symm
  have h4 := pow_lt_pow_right₀ hq haN
  have h7 := Nat.eq_zero_of_dvd_of_lt h2 (by
    have := Nat.one_le_pow a (normV v) (by omega)
    omega)
  by_contra h
  have := one_lt_pow₀ hq h
  omega

end GlobalTheory.CompanionTheory.TameAction
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSectionsCotangentIndep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem cotangent_independent_unit_mul {R : Type} [CommRing R] [IsLocalRing R] {d : ℕ}
    (a a' : Fin d → R) (w : Rˣ) (h : ∀ j, a' j = w * a j)
    (hl : LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R))) :
    LinearIndependent (ResidueField R) (fun j : {j : Fin d // a' j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) := by
  classical
  have hmem : ∀ j, a' j ∈ maximalIdeal R ↔ a j ∈ maximalIdeal R := fun j => by
    rw [h j]; exact Ideal.unit_mul_mem_iff_mem _ w.isUnit
  let e : {j : Fin d // a j ∈ maximalIdeal R} ≃ {j : Fin d // a' j ∈ maximalIdeal R} :=
    Equiv.subtypeEquivRight (fun j => (hmem j).symm)
  have hu : IsUnit (IsLocalRing.residue R (w : R)) := w.isUnit.map _
  have key : (fun j : {j : Fin d // a' j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) =
      (fun j => hu.unit • ((maximalIdeal R).toCotangent ⟨_, (e.symm j).2⟩ : CotangentSpace R)) := by
    funext j
    obtain ⟨j, hj⟩ := j
    have hj' : a j ∈ maximalIdeal R := (hmem j).1 hj
    have hsub : (⟨a' j, hj⟩ : maximalIdeal R) = (w : R) • (⟨a j, hj'⟩ : maximalIdeal R) :=
      Subtype.ext (by simp [h j])
    show (maximalIdeal R).toCotangent ⟨a' j, hj⟩ = hu.unit • (maximalIdeal R).toCotangent ⟨a j, hj'⟩
    rw [hsub, map_smul, Units.smul_def, IsUnit.unit_spec, ← IsLocalRing.ResidueField.algebraMap_eq,
      algebraMap_smul]
  rw [key]
  exact (hl.units_smul (fun _ => hu.unit)).comp e.symm e.symm.injective

theorem germ_chart_eq {X : Scheme.{0}} {L : LB X} (s : L.Sec) (i c : L.ι) {x : X}
    (hi : x ∈ L.U i) (hc : x ∈ L.U c) :
    X.presheaf.germ (L.U i) x hi (s.f i) =
      X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩ (L.g i c : Γ(X, L.U i ⊓ L.U c)) *
        X.presheaf.germ (L.U c) x hc (s.f c) := by
  have e1 := congrArg (X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩) (s.compat i c)
  rw [map_mul] at e1
  have r1 : X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩
      (X.presheaf.map (homOfLE inf_le_left : L.U i ⊓ L.U c ⟶ L.U i).op (s.f i)) =
      X.presheaf.germ (L.U i) x hi (s.f i) :=
    X.presheaf.germ_res_apply (homOfLE inf_le_left) x ⟨hi, hc⟩ (s.f i)
  have r2 : X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩
      (X.presheaf.map (homOfLE inf_le_right : L.U i ⊓ L.U c ⟶ L.U c).op (s.f c)) =
      X.presheaf.germ (L.U c) x hc (s.f c) :=
    X.presheaf.germ_res_apply (homOfLE inf_le_right) x ⟨hi, hc⟩ (s.f c)
  rw [← r1, ← r2]
  exact e1

theorem sum_smul_f {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : Fin n → Γ(X, ⊤)) (b : Fin n → L.Sec)
    (c : L.ι) : (∑ p, a p • b p).f c = ∑ p, resG X le_top (a p) * (b p).f c := by
  let φ : L.Sec →+ Γ(X, L.U c) :=
    { toFun := fun s => s.f c, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact (map_sum φ (fun p => a p • b p) Finset.univ).trans (Finset.sum_congr rfl fun p _ => rfl)

theorem resG_algebraMap (Y : Var ℂ) (V : Y.X.Opens) (a : ℂ) :
    resG Y.X (le_top : V ≤ ⊤) (algebraMap ℂ Γ(Y.X, ⊤) a) =
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V a := by
  rfl

theorem algX_smooth (Y : Var ℂ) {V : Y.X.Opens} (hV : IsAffineOpen V) :
    (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V).Smooth := by
  haveI := Y.smooth_str
  have hsm : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim Y.str
  have e : V ≤ Y.str ⁻¹ᵁ ⊤ := by simp
  have happ := HasRingHomProperty.appLE @Smooth Y.str hsm ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ e
  have heq : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V =
      (Y.str.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := by
    ext a
    rw [← resG_algebraMap, GlobalTheory.ProjVar.Var.algebraMap_Γ]
    rfl
  rw [heq]
  exact (RingHom.Smooth.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
    (Y.str.appLE ⊤ V e)).mpr happ

theorem bertini_on_affine (Y : Var ℂ) (L : LB Y.X) (n d : ℕ) (b : Fin n → L.Sec) (c : L.ι)
    {V : Y.X.Opens} (hV : IsAffineOpen V) (hVc : V ≤ L.U c) :
    ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧
      ∀ u : Fin d × Fin n → ℂ, MvPolynomial.eval u Q ≠ 0 →
      ∀ (x : Y.X) (hx : x ∈ V), (∃ p, x ∈ nonzeroLocus (b p)) →
        LinearIndependent (ResidueField (Y.X.presheaf.stalk x))
          (fun j : {j : Fin d // Y.X.presheaf.germ (L.U c) x (hVc hx)
              ((∑ p, algebraMap ℂ Γ(Y.X, ⊤) (u (j, p)) • b p).f c) ∈
                maximalIdeal (Y.X.presheaf.stalk x)} =>
            ((maximalIdeal (Y.X.presheaf.stalk x)).toCotangent ⟨_, j.2⟩ :
              CotangentSpace (Y.X.presheaf.stalk x))) := by
  classical
  letI : Algebra ℂ Γ(Y.X, V) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V).toAlgebra
  haveI : Algebra.Smooth ℂ Γ(Y.X, V) := algX_smooth Y hV
  obtain ⟨Q, hQ, hQu⟩ := GlobalTheory.bertini_cotangent_independent ℂ Γ(Y.X, V)
    (fun p : Fin n => resG Y.X hVc ((b p).f c)) d
  refine ⟨Q, hQ, fun u hu x hx hnz => ?_⟩
  have hgres : ∀ {U W : Y.X.Opens} (h : W ≤ U) (hxW : x ∈ W) (z : Γ(Y.X, U)),
      Y.X.presheaf.germ W x hxW (resG Y.X h z) = Y.X.presheaf.germ U x (h hxW) z :=
    fun h hxW z => Y.X.presheaf.germ_res_apply (homOfLE h) x hxW z
  have hgs : ∀ {U : Y.X.Opens} (hxU : x ∈ U) (z : Γ(Y.X, U)),
      gs (𝟙 Y.X) x U z = Y.X.presheaf.germ U x hxU z := by
    intro U hxU z
    simp [gs, hxU]
    rfl
  let x' : V := ⟨x, hx⟩
  let q := (hV.primeIdealOf x').asIdeal
  letI : Algebra Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) :=
    TopCat.Presheaf.algebra_section_stalk Y.X.presheaf x'
  haveI := hV.isLocalization_stalk x'
  have hf : ∃ p, resG Y.X hVc ((b p).f c) ∉ q := by
    obtain ⟨p, hp⟩ := hnz
    obtain ⟨k, hk, hunit⟩ := (mem_nonzeroLocus (b p) x).1 hp
    rw [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_sec L (b p) k c x hk (hVc hx)] at hunit
    have hu2 : IsUnit (Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c)) := by
      rw [← hgs (hVc hx)]; exact isUnit_of_mul_isUnit_right hunit
    refine ⟨p, fun hmem => ?_⟩
    have h0 := (GlobalTheory.residue_algebraMap_eq_zero_iff_mem (R := Y.X.presheaf.stalk (x' : Y.X)) q _).2 hmem
    have e2 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (resG Y.X hVc ((b p).f c)) =
        Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c) := hgres hVc hx _
    rw [e2, IsLocalRing.residue_eq_zero_iff] at h0
    exact h0 hu2
  have hLI := hQu u hu q (Y.X.presheaf.stalk (x' : Y.X)) hf
  refine cotangent_independent_unit_mul _ _ 1 (fun j => ?_) hLI
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Units.val_one, one_mul, sum_smul_f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Algebra.smul_def, map_mul, map_mul]
  have e1 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (algebraMap ℂ Γ(Y.X, V) (u (j, p))) =
      Y.X.presheaf.germ (L.U c) x (hVc hx) (resG Y.X le_top (algebraMap ℂ Γ(Y.X, ⊤) (u (j, p)))) := by
    show Y.X.presheaf.germ V x hx (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V (u (j, p))) = _
    rw [← resG_algebraMap, hgres, hgres]
  have e2 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (resG Y.X hVc ((b p).f c)) =
      Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c) := hgres hVc hx _
  rw [e1, e2]

theorem bertini_cotIndep : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∀ (n d : ℕ) (b : Fin n → L.Sec), (⨆ j, nonzeroLocus (b j) = ⊤) → ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧ ∀ C : Fin d → Fin n → ℂ, MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 → CotIndep (fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j) := by
  intro Y L hL n d b hb
  classical
  haveI : CompactSpace Y.X := (Var.isNoetherian_X Y).toCompactSpace
  obtain ⟨m, V, c, hVa, hVc, hcov⟩ := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_affine_chart_cover L hL
  choose Q hQ hQu using fun k : Fin m => bertini_on_affine Y L n d b (c k) (hVa k) (hVc k)
  refine ⟨∏ k, Q k, Finset.prod_ne_zero_iff.2 fun k _ => hQ k, fun C hC => ?_⟩
  intro x i hx
  have hCk : ∀ k, MvPolynomial.eval (fun p => C p.1 p.2) (Q k) ≠ 0 := by
    intro k
    rw [map_prod] at hC
    exact Finset.prod_ne_zero_iff.1 hC k (Finset.mem_univ _)
  have hxV : x ∈ ⨆ k, V k := by rw [hcov]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hxV
  have hnz : ∃ p, x ∈ nonzeroLocus (b p) := by
    have : x ∈ ⨆ j, nonzeroLocus (b j) := by rw [hb]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have h6 := hQu k (fun p => C p.1 p.2) (hCk k) x hk hnz
  refine cotangent_independent_unit_mul _ _
    (IsUnit.map (ConcreteCategory.hom (Y.X.presheaf.germ (L.U i ⊓ L.U (c k)) x ⟨hx, hVc k hk⟩))
      (L.g i (c k)).isUnit).unit (fun j => ?_) h6
  rw [IsUnit.unit_spec]
  exact germ_chart_eq _ i (c k) hx (hVc k hk)

end GlobalTheory.CompanionTheory.KoszulCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.CuspBridge

theorem unipGL_eq_unip {R : Type} [CommRing R] {a r : ℕ} (X : AutomorphicForm.UPos a r → R) :
    AutomorphicForm.unipGL X = unip X := by
  apply Units.ext
  rfl

theorem isAddHaarMeasure_unipMeasure (E : Type) [Field E] [NumberField E] (a r : ℕ) :
    (AutomorphicForm.unipMeasure E a r).IsAddHaarMeasure := by
  infer_instance

theorem isCuspidal_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → AutomorphicForm.IsCuspidal φ.1 := by
  intro E _ _ _ a φ h r h0 h1 g
  have h2 := h.2 r h0 h1 (AutomorphicForm.unipMeasure E a r) (AutomorphicForm.unipFundamentalDomain E a r)
    (isAddHaarMeasure_unipMeasure E a r) AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain g
  simpa only [AutomorphicForm.constantTerm, unipGL_eq_unip] using h2

end GlobalTheory.CompanionTheory.CuspBridge

end
end

