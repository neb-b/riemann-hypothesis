module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CcDualWtAnti
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0013
public import Lemmata.DualWeylPullback.DualWeylPull
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0014

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudC
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility

section

variable {p n' : ℕ} {R : RS p n'} {m : ℕ}

theorem cc_elem (X : Fin n' → Fin (m + 1) → ℤ) (e : Edge R.W R.Qq (m + 1))
    (G : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf)
    (hs : (fun s : Fin n' => extO R.O R.ι R.σ s.val e.src) = famD R.O G 1)
    (hle : (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e) = famD R.O G (algebraMap R.O R.Kf R.w))
    (x : Vsp R.Kf X) (h1 : ((1 : R.Kf) ^ Ar 1 X) • x ∈ toV X (Hten R.O X (famD R.O G 1)))
    (hw : ((algebraMap R.O R.Kf R.w) ^ Ar 1 X) • x ∈ toV X (Hten R.O X (famD R.O G (algebraMap R.O R.Kf R.w)))) :
    x ∈ HL (O := R.O) R.ι R.σ X e.src ∧ x ∈ Re p R.ι R.σ R.w 1 X e := by
  constructor
  · show x ∈ toV X (Hten R.O X (fun s : Fin n' => extO R.O R.ι R.σ s.val e.src))
    rw [hs]
    rwa [one_zpow, one_smul] at h1
  · refine (cc_mem_scale (zpow_ne_zero _ R.w_ne)).2 ?_
    rw [zpow_neg, inv_inv]
    show _ ∈ toV X (Hten R.O X (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e))
    rw [hle]
    exact hw

end

theorem restCloudMaps_of (h : RestCloudLat) (hIncl : DualHeightInclusion) : RestCloudMaps := by
  classical
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 e he
  obtain ⟨mH, mU, abelian₂, hint, hel⟩ :=
    h p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 _ _ _ _ _ rfl rfl rfl rfl rfl
  obtain ⟨G, hG, hs, hle, ht⟩ := cc_edge R e he
  obtain ⟨nb, z0, s, s', ka, hnb, hka, h24, hmem⟩ := hel G hG
  have hw : algebraMap R.O R.Kf R.w ≠ 0 := R.w_ne
  have hIH : IntB R mH := fun M hM => (hint M hM).1
  have hIU : IntB R mU := fun M hM => (hint M hM).2.1
  have hIL : IntB R abelian₂ := fun M hM => (hint M hM).2.2

  obtain ⟨hlo1, hlo2⟩ := cc_lo TT ccl aw bw lam0 A B hBase hzero hAB
  obtain ⟨hlo1', hlo2'⟩ := cc_dualW TT _ _ hlo1 hlo2
  have hze1 : ∀ s ∈ TT, flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s 0 = ((2 * ccl : ℕ) : ℤ) ∧
      flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s (Fin.last (mm + 1)) = -((2 * ccl : ℕ) : ℤ) :=
    fun s hs => ⟨cc_flat_zero _ _ _ s hs, cc_flat_last _ _ _ s hs⟩
  obtain ⟨aze, -⟩ := cc_Ar_of TT _ _ hze1 (fun s hs => cc_flat_off _ _ _ s hs)
  obtain ⟨alo, -⟩ := cc_Ar_of TT _ _ hlo1 hlo2
  obtain ⟨alo', elo'⟩ := cc_Ar_of TT _ _ hlo1' hlo2'
  have aHp : Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) =
      Ar 1 (flatW (mm + 1) A B) + Ar 1 (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)) := by
    rw [← cc_Ar_add, ← cc_flat_add]
  have alam : Ar 1 lam0 = Ar 1 (flatW (mm + 1) A B) + Ar 1 (lam0 - flatW (mm + 1) A B) := by
    rw [← cc_Ar_add, add_sub_cancel]
  have aL : Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) =
      Ar 1 lam0 + Ar 1 (dualW (lam0 - flatW (mm + 1) A B)) := by
    rw [aHp, alam, aze, alo, alo']
    push_cast
    ring
  have hdlo : IsDominant (lam0 - flatW (mm + 1) A B) := cc_lo_dom TT ccl aw bw lam0 A B hBase hDom hzero hAB
  have hdlo' : IsDominant (dualW (lam0 - flatW (mm + 1) A B)) := fun s => cc_dualWt_anti _ (hdlo s)

  obtain ⟨z1, sb1, sa1, -⟩ := hmem 1 one_ne_zero
  obtain ⟨zw, sbw, saw, isow⟩ := hmem _ hw
  obtain ⟨-, -, sap, -⟩ := hmem _ (mul_ne_zero hw hw)
  obtain ⟨hz1, hz2⟩ := cc_elem _ e G hs hle z0 z1 zw
  refine ⟨nb, mH.flip z0, fun b => mU.flip (s b), fun a' => abelian₂.flip (s' a'), ka, hnb, hka, ?_, ?_, ?_⟩
  · intro a' b F
    exact h24 a' b F
  · intro F
    constructor
    · intro hF
      have h1 := (cc_mem_scale (zpow_ne_zero _ hw)).1 hF
      rw [zpow_neg, inv_inv] at h1
      have h2 : mH ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) A B)) • F)
          ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl))) • z0) =
          (algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl))) •
            mH.flip z0 F := by
        rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, ← zpow_add₀ hw, aHp, LinearMap.flip_apply,
          add_comm (Ar 1 (flatW (mm + 1) A B))]
      have h3 := isow ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) A B)) • F) (by
        rw [h2, ← hle]
        exact h1)
      refine (cc_mem_scale (zpow_ne_zero _ hw)).2 ?_
      rw [zpow_neg, inv_inv]
      show _ ∈ toV _ (Hten R.O _ (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e))
      rw [hle]
      exact h3
    · intro hF
      exact cc_Re hIH aHp e he F hF z0 hz2
  · intro t c₂ hc
    refine ⟨?_, ?_, ?_⟩
    · intro F hF
      exact cc_CCL hIncl hIH aHp (flattened_weight_dominant _ _ _) e he z0 hz1 hz2 t c₂ F hF
    · intro b F hF
      obtain ⟨hb1, hb2⟩ := cc_elem _ e G hs hle (s b) (sb1 b) (sbw b)
      exact cc_CCL hIncl hIU alam hdlo e he (s b) hb1 hb2 t c₂ F hF
    · intro a' g hg
      obtain ⟨-, ha2⟩ := cc_elem _ e G hs hle (s' a') (sa1 a') (saw a')
      have ha3 : ((algebraMap R.O R.Kf R.w * algebraMap R.O R.Kf R.w) ^ Ar 1 (dualW (lam0 - flatW (mm + 1) A B))) • s' a' ∈
          HL (O := R.O) R.ι R.σ (dualW (lam0 - flatW (mm + 1) A B)) e.tgt := by
        show _ ∈ toV _ (Hten R.O _ (fun s : Fin n' => extO R.O R.ι R.σ s.val e.tgt))
        rw [ht]
        exact sap a'
      have h5 := cc_CCL' hIL aL hdlo' (by rw [elo', alo']) (TT.card * ccl) (by rw [alo']; push_cast; ring) e he (s' a')
        ha3 ha2 t c₂ (by rw [← mul_assoc]; exact hc) g hg
      rw [← mul_assoc] at h5
      exact h5

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIso
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem nuOf_add {m : ℕ} (lam mu : Fin (m + 1) → ℤ) (h1 : Antitone lam) (h2 : Antitone mu) :
    nuOf (lam + mu) = nuOf lam + nuOf mu := by
  funext t
  have a1 : lam (Fin.last m) ≤ lam t := h1 (Fin.le_last t)
  have a2 : mu (Fin.last m) ≤ mu t := h2 (Fin.le_last t)
  simp only [nuOf, Pi.add_apply]
  omega

section One

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem smulO_eq {σ : Type} (a : O) (F : MvPolynomial σ K) : a • F = algebraMap O K a • F :=
  (algebraMap_smul K a F).symm

theorem exists_pow_mem (w : O) (hw : Irreducible w) (m : ℕ) (mu : Fin (m + 1) → ℤ) (hmu : Antitone mu)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (hF : F ∈ dualWeyl K (m + 1) (m + 1) (nuOf mu)) : ∃ n : ℕ, w ^ n • F ∈ H0 O m mu (colSpan O g) := by
  first | exact Bl.DualWeylPullback.goal1 .. | (apply Bl.DualWeylPullback.goal1 <;> assumption) | (intros; apply Bl.DualWeylPullback.goal1 <;> assumption) | (apply @Bl.DualWeylPullback.goal1 <;> assumption) | (intros; apply @Bl.DualWeylPullback.goal1 <;> assumption) | (apply @Bl.DualWeylPullback.goal1 <;> first | assumption | infer_instance) | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g hg F hF | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g hg F | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g hg | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› | exact @Bl.DualWeylPullback.goal1 O K | exact @Bl.DualWeylPullback.goal1 O

theorem iso_one (hCD : CartanDomain) (w : O) (hw : Irreducible w) (m : ℕ) (mu ze : Fin (m + 1) → ℤ) (hmu : Antitone mu)
    (hze : Antitone ze) (Λ : Submodule O (Fin (m + 1) → K)) (hΛ : IsLattice O Λ)
    (z : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (hz : z ∈ H0 O m ze Λ)
    (hprim : ¬ ∃ z' ∈ H0 O m ze Λ, z = w • z') (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (hF : F ∈ dualWeyl K (m + 1) (m + 1) (nuOf mu)) (hzF : z * F ∈ H0 O m (mu + ze) Λ) : F ∈ H0 O m mu Λ := by
  have hwK : algebraMap O K w ≠ 0 := by
    intro h
    exact hw.ne_zero ((IsFractionRing.injective O K) (by rw [h, map_zero]))
  have key : ∀ n : ℕ, ∀ F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, w ^ n • F ∈ H0 O m mu Λ →
      z * F ∈ H0 O m (mu + ze) Λ → F ∈ H0 O m mu Λ := by
    intro n
    induction n with
    | zero => intro F h _; simpa using h
    | succ n ih =>
      intro F h1 h2
      apply ih F _ h2
      have hX : (w ^ (n + 1) • F) * z = w • (w ^ n • (z * F)) := by
        rw [smul_mul_assoc, pow_succ', mul_smul, mul_comm F z]
      rcases hCD O K w hw m mu ze Λ hΛ hmu hze _ h1 z hz ⟨_, Submodule.smul_mem _ _ h2, hX⟩ with ⟨F', hF', he⟩ | h
      · have : w ^ n • F = F' := by
          rw [pow_succ', mul_smul, smulO_eq w, smulO_eq w F'] at he
          exact smul_right_injective _ hwK he
        rw [this]; exact hF'
      · exact absurd h hprim
  obtain ⟨g, hg, rfl⟩ := hΛ
  obtain ⟨n, hn⟩ := exists_pow_mem w hw m mu hmu g hg F hF
  exact key n F hn hzF

theorem retract_one (hCD : CartanDomain) (hCO : CartanOnto) (w : O) (hw : Irreducible w) (m : ℕ)
    (mu ze : Fin (m + 1) → ℤ) (hmu : Antitone mu)
    (hze : Antitone ze) (Λ : Submodule O (Fin (m + 1) → K)) (hΛ : IsLattice O Λ)
    (z : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (hz : z ∈ H0 O m ze Λ)
    (hprim : ¬ ∃ z' ∈ H0 O m ze Λ, z = w • z') :
    ∃ ρ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K,
      (∀ G ∈ H0 O m (mu + ze) Λ, ρ G ∈ H0 O m mu Λ) ∧
      ∀ F ∈ dualWeyl K (m + 1) (m + 1) (nuOf mu), ρ (z * F) = F := by
  classical
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hΛ' := hΛ
  obtain ⟨g, hg, rfl⟩ := hΛ
  have hsum : Antitone (mu + ze) := hmu.add hze
  obtain ⟨B, -, hB1, hB3, hB2⟩ := la_basis hinj m mu g hg
  obtain ⟨B', -, hB1', hB3', hB2'⟩ := la_basis hinj m (mu + ze) g hg
  rw [← H0_eq_twisted_nabla (la_indep hinj) m mu hmu g hg] at hB1
  rw [← H0_eq_twisted_nabla (la_indep hinj) m (mu + ze) hsum g hg] at hB1'
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf mu)) := (sSIdxFinite _ _ _).fintype
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (mu + ze))) := (sSIdxFinite _ _ _).fintype
  let b : Module.Basis _ K (dualWeyl K (m + 1) (m + 1) (nuOf mu)) :=
    (Module.Basis.span hB3).map (LinearEquiv.ofEq _ _ hB2)
  let b' : Module.Basis _ K (dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze))) :=
    (Module.Basis.span hB3').map (LinearEquiv.ofEq _ _ hB2')
  have hb : ∀ i, (b i : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = B i := by
    intro i
    simp [b, Module.Basis.span_apply]
  have hb' : ∀ i, (b' i : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = B' i := by
    intro i
    simp [b', Module.Basis.span_apply]
  have hmem : ∀ F : dualWeyl K (m + 1) (m + 1) (nuOf mu),
      F ∈ Submodule.span O (Set.range b) ↔ (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ H0 O m mu (colSpan O g) := by
    intro F
    have e : (Submodule.span O (Set.range b)).map ((dualWeyl K (m + 1) (m + 1) (nuOf mu)).subtype.restrictScalars O) =
        H0 O m mu (colSpan O g) := by
      rw [Submodule.map_span, ← Set.range_comp, ← hB1]
      congr 2
      funext i
      exact hb i
    rw [← e]
    constructor
    · intro h; exact ⟨F, h, rfl⟩
    · rintro ⟨F', h, he⟩
      have : F' = F := Subtype.ext he
      rwa [← this]
  have hmem' : ∀ F : dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)),
      F ∈ Submodule.span O (Set.range b') ↔
        (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ H0 O m (mu + ze) (colSpan O g) := by
    intro F
    have e : (Submodule.span O (Set.range b')).map
        ((dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze))).subtype.restrictScalars O) = H0 O m (mu + ze) (colSpan O g) := by
      rw [Submodule.map_span, ← Set.range_comp, ← hB1']
      congr 2
      funext i
      exact hb' i
    rw [← e]
    constructor
    · intro h; exact ⟨F, h, rfl⟩
    · rintro ⟨F', h, he⟩
      have : F' = F := Subtype.ext he
      rwa [← this]
  have hzK : z ∈ dualWeyl K (m + 1) (m + 1) (nuOf ze) := la_nablaLTw_le m ze g hg z (H0_le_twisted_nabla m ze hze g hg hz)
  let io : dualWeyl K (m + 1) (m + 1) (nuOf mu) →ₗ[K] dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)) :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft K z) ∘ₗ (dualWeyl K (m + 1) (m + 1) (nuOf mu)).subtype) (by
      intro F
      rw [nuOf_add mu ze hmu hze, add_comm (nuOf mu) (nuOf ze)]
      exact dualWeyl_mul K _ _ _ _ hzK F.2)
  have hio : ∀ F, (io F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = z * F := fun F => rfl
  obtain ⟨ret, hr1, hr2⟩ := KP.latRetract b b' io (by
    intro F
    rw [hmem, hmem', hio]
    constructor
    · intro h
      exact iso_one hCD w hw m mu ze hmu hze _ hΛ' z hz hprim F F.2 h
    · intro h
      rw [hCO O K m mu ze _ hΛ' hmu hze]
      exact Submodule.subset_span ⟨F, h, z, hz, mul_comm _ _⟩)
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_extend ((dualWeyl K (m + 1) (m + 1) (nuOf mu)).subtype ∘ₗ ret)
  have hρ' : ∀ G : dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)),
      ρ (G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = (ret G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
    fun G => LinearMap.congr_fun hρ G
  refine ⟨ρ, ?_, ?_⟩
  · intro G hG
    have hGK : G ∈ dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)) :=
      la_nablaLTw_le m _ g hg G (H0_le_twisted_nabla m _ hsum g hg hG)
    rw [hρ' ⟨G, hGK⟩, ← hmem]
    exact hr2 _ ((hmem' ⟨G, hGK⟩).2 hG)
  · intro F hF
    have := hρ' (io ⟨F, hF⟩)
    rw [hio] at this
    rw [this, hr1]

end One

theorem iso_ten {O K : Type} [CommRing O] [Field K] [Algebra O K] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}
    (V : S → Submodule K (MvPolynomial (Fin k × Fin n) K)) (N Np : S → Submodule O (MvPolynomial (Fin k × Fin n) K))
    (z : S → MvPolynomial (Fin k × Fin n) K)
    (ρ : S → MvPolynomial (Fin k × Fin n) K →ₗ[K] MvPolynomial (Fin k × Fin n) K)
    (h1 : ∀ s, ∀ G ∈ Np s, ρ s G ∈ N s) (h2 : ∀ s, ∀ F ∈ V s, ρ s (z s * F) = F)
    (F : MvPolynomial (S × (Fin k × Fin n)) K) (hF : F ∈ tensorLat K K V)
    (hzF : (∏ s, blockEmb K s (z s)) * F ∈ tensorLat O K Np) : F ∈ tensorLat O K N := by
  obtain ⟨T, hT⟩ := KP.tensorMap (K := K) (S := S) (α := Fin k × Fin n)
    (fun s => (blockEmb K (k := k) (n := n) s).toLinearMap ∘ₗ ρ s)
  have hT' : ∀ P : S → MvPolynomial (Fin k × Fin n) K,
      T (∏ s, blockEmb K s (P s)) = ∏ s, blockEmb K s (ρ s (P s)) := fun P => hT P
  have hA : ∀ G ∈ tensorLat O K Np, T G ∈ tensorLat O K N := by
    intro G hG
    unfold tensorLat at hG
    refine Submodule.span_induction (p := fun G _ => T G ∈ tensorLat O K N) ?_ ?_ ?_ ?_ hG
    · rintro _ ⟨P, hP, rfl⟩
      rw [hT']
      exact Submodule.subset_span ⟨fun s => ρ s (P s), fun s => h1 s _ (hP s), rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [← algebraMap_smul K c x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ _ hx
  have hB : ∀ F ∈ tensorLat K K V, T ((∏ s, blockEmb K s (z s)) * F) = F := by
    intro F hF
    unfold tensorLat at hF
    refine Submodule.span_induction (p := fun F _ => T ((∏ s, blockEmb K s (z s)) * F) = F) ?_ ?_ ?_ ?_ hF
    · rintro _ ⟨P, hP, rfl⟩
      rw [← Finset.prod_mul_distrib]
      have : (∏ s, blockEmb K s (z s) * blockEmb K s (P s)) = ∏ s, blockEmb K s (z s * P s) :=
        Finset.prod_congr rfl fun s _ => (map_mul _ _ _).symm
      rw [this, hT']
      exact Finset.prod_congr rfl fun s _ => by rw [h2 s _ (hP s)]
    · rw [mul_zero, map_zero]
    · intro x y _ _ hx hy
      rw [mul_add, map_add (f := _), hx, hy]
    · intro c x _ hx
      rw [mul_smul_comm, map_smul, hx]
  rw [← hB F hF]
  exact hA _ hzF

theorem cloudIso (hCD : CartanDomain) (hCO : CartanOnto) : CloudIsoP := by
  classical
  intro O K _ _ _ _ _ _ w hw n' m mu ze hmu hze M hM z hz hprim F hF hzF
  choose ρ hρ1 hρ2 using fun s =>
    retract_one hCD hCO w hw m (mu s) (ze s) (hmu s) (hze s) (M s) (hM s) (z s) (hz s) (hprim s)
  exact iso_ten (fun s => dualWeyl K (m + 1) (m + 1) (nuOf (mu s))) (fun s => H0 O m (mu s) (M s))
    (fun s => H0 O m (mu s + ze s) (M s)) z ρ hρ1 hρ2 F hF hzF

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LamPolySmulRight
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def PosOK {p n' : ℕ} (R : RS p n') (m : ℕ) (lam mu mup ze lo lo' : Fin (m + 1) → ℤ) (d : ℚ) (κ : ℕ) : Prop :=
  ∃ abelian₂ : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
    (∀ v ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf lam), ∀ t ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf lo'),
      abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf mup)) ∧
    (∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∀ v ∈ H0 R.O m lam Λ, ∀ t ∈ H0 R.O m lo' Λ,
      abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈ H0 R.O m mup Λ) ∧
    ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf, IsUnit g.det →
      ∃ (nb : ℕ) (z0 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
        (s s' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = d ∧ (∀ b, ka b ≤ κ) ∧
        (∀ a' b, ∀ F ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf mu),
          abelian₂ (blockEmb R.Kf true (F * s b) * blockEmb R.Kf false (s' a')) =
            if a' = b then ((p : R.Kf) ^ ka b) • (z0 * F) else 0) ∧
        ∀ c : R.Kf, c ≠ 0 →
          (c ^ (ze 0)) • z0 ∈ H0 R.O m ze (colSpan R.O (g * lb_D _ 1 c)) ∧
          (¬ ∃ z' ∈ H0 R.O m ze (colSpan R.O (g * lb_D _ 1 c)), (c ^ (ze 0)) • z0 = R.w • z') ∧
          (∀ b, (c ^ (lo 0)) • s b ∈ H0 R.O m lo (colSpan R.O (g * lb_D _ 1 c))) ∧
          (∀ a', (c ^ (lo' 0)) • s' a' ∈ H0 R.O m lo' (colSpan R.O (g * lb_D _ 1 c)))

section Gen

variable {K : Type} [Field K] {S α : Type} [Fintype S]

theorem prod_bE_smul {k n : ℕ} (a : S → K) (f : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (a s • f s) = (∏ s, a s) • ∏ s, blockEmb K s (f s) := by
  simp only [Algebra.smul_def, map_mul, AlgHom.commutes, Finset.prod_mul_distrib, map_prod]

def renB (K : Type) [Field K] (S α : Type) (b : Bool) : MvPolynomial (S × α) K →ₐ[K] MvPolynomial (S × (Bool × α)) K :=
  rename fun x => (x.1, (b, x.2))

theorem renB_prod {k n : ℕ} (v t : S → MvPolynomial (Fin k × Fin n) K) :
    renB K S (Fin k × Fin n) true (∏ s, blockEmb K s (v s)) * renB K S (Fin k × Fin n) false (∏ s, blockEmb K s (t s)) =
      ∏ s, rename (fun x : Bool × (Fin k × Fin n) => (s, x)) (blockEmb K true (v s) * blockEmb K false (t s)) := by
  simp only [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [renB, blockEmb, map_mul, rename_rename]
  try rfl

end Gen

section LamPoly

variable {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}

def lamPoly (T : MvPolynomial (S × (Bool × (Fin k × Fin n))) K →ₗ[K] MvPolynomial (S × (Fin k × Fin n)) K)
    (V W : MvPolynomial (S × (Fin k × Fin n)) K) : MvPolynomial (S × (Fin k × Fin n)) K :=
  T (renB K S (Fin k × Fin n) true V * renB K S (Fin k × Fin n) false W)

variable (T : MvPolynomial (S × (Bool × (Fin k × Fin n))) K →ₗ[K] MvPolynomial (S × (Fin k × Fin n)) K)

theorem lamPoly_add_left (V V' W) : lamPoly T (V + V') W = lamPoly T V W + lamPoly T V' W := by
  unfold lamPoly
  rw [map_add (f := _), add_mul, map_add (f := _)]

theorem lamPoly_add_right (V W W') : lamPoly T V (W + W') = lamPoly T V W + lamPoly T V W' := by
  unfold lamPoly
  rw [map_add (f := _), mul_add, map_add (f := _)]

theorem lamPoly_smul_left (c : K) (V W) : lamPoly T (c • V) W = c • lamPoly T V W := by
  unfold lamPoly
  rw [map_smul, smul_mul_assoc, map_smul]

theorem lamPoly_smul_right (c : K) (V W) : lamPoly T V (c • W) = c • lamPoly T V W := by
  unfold lamPoly
  rw [map_smul, mul_smul_comm, map_smul]

theorem lamPoly_zero_left (W) : lamPoly T 0 W = 0 := by
  simp [lamPoly]

theorem lamPoly_zero_right (V) : lamPoly T V 0 = 0 := by
  simp [lamPoly]

variable (L : S → MvPolynomial (Bool × (Fin k × Fin n)) K →ₗ[K] MvPolynomial (Fin k × Fin n) K)
  (hT : ∀ Q : S → MvPolynomial (Bool × (Fin k × Fin n)) K,
    T (∏ s, rename (fun x => (s, x)) (Q s)) = ∏ s, blockEmb K s (L s (Q s)))

include hT in
theorem lamPoly_prod (v t : S → MvPolynomial (Fin k × Fin n) K) :
    lamPoly T (∏ s, blockEmb K s (v s)) (∏ s, blockEmb K s (t s)) =
      ∏ s, blockEmb K s (L s (blockEmb K true (v s) * blockEmb K false (t s))) := by
  unfold lamPoly
  rw [renB_prod, hT]


include hT in
theorem lamPoly_mem {A : Type} [CommRing A] [Algebra A K] (Mv Mt Mr : S → Submodule A (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ v ∈ Mv s, ∀ t ∈ Mt s, L s (blockEmb K true v * blockEmb K false t) ∈ Mr s) :
    ∀ V ∈ tensorLat A K Mv, ∀ W ∈ tensorLat A K Mt, lamPoly T V W ∈ tensorLat A K Mr := by
  intro V hV W hW
  induction hV using Submodule.span_induction with
  | mem V hV0 =>
    induction hW using Submodule.span_induction with
    | mem W hW0 =>
      obtain ⟨F, hF, rfl⟩ := hV0
      obtain ⟨G, hG, rfl⟩ := hW0
      rw [lamPoly_prod T L hT]
      exact Submodule.subset_span ⟨fun s => L s (blockEmb K true (F s) * blockEmb K false (G s)),
        fun s => h s _ (hF s) _ (hG s), rfl⟩
    | zero => rw [lamPoly_zero_right]; exact Submodule.zero_mem _
    | add W W' _ _ h1 h2 => rw [lamPoly_add_right]; exact Submodule.add_mem _ h1 h2
    | smul a W _ h1 =>
      rw [← algebraMap_smul K a W, lamPoly_smul_right, algebraMap_smul]
      exact Submodule.smul_mem _ a h1
  | zero => rw [lamPoly_zero_left]; exact Submodule.zero_mem _
  | add V V' _ _ h1 h2 => rw [lamPoly_add_left]; exact Submodule.add_mem _ h1 h2
  | smul a V _ h1 =>
    rw [← algebraMap_smul K a V, lamPoly_smul_left, algebraMap_smul]
    exact Submodule.smul_mem _ a h1

end LamPoly

theorem cbNuOf_add {m : ℕ} (a b : Fin (m + 1) → ℤ) (ha : Antitone a) (hb : Antitone b) :
    nuOf (a + b) = nuOf a + nuOf b := by
  funext t
  simp only [nuOf, Pi.add_apply]
  have h1 : a (Fin.last m) ≤ a t := ha (Fin.le_last t)
  have h2 : b (Fin.last m) ≤ b t := hb (Fin.le_last t)
  omega

theorem Ar_one {n' m : ℕ} (X : Fin n' → Fin (m + 1) → ℤ) : Ar 1 X = ∑ s, lamAt X s 0 := by
  unfold Ar
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single_of_mem (0 : Fin (m + 1)) (by simp)]
  intro b hb hb0
  exfalso
  apply hb0
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact Fin.ext (by rw [Fin.val_zero]; omega)

theorem famD_lat (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' k : ℕ}
    (gs : Fin n' → Matrix (Fin k) (Fin k) Kf) (hgs : ∀ s, IsUnit (gs s).det) (c : Kf) (hc : c ≠ 0) (s : Fin n') :
    IsLattice O (famD O gs c s) :=
  ⟨gs s * lb_D k 1 c, by rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det k 1 c hc), rfl⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

