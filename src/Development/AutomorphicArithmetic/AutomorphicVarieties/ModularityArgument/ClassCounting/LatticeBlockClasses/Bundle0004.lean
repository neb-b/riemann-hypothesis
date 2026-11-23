module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBetaDiv
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl Polynomial

private theorem shift_sum (p : ℤ[X]) (a : ℤ) (d : ℕ → ℤ) :
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (d (i + 1) - a * d i) =
      ∑ i ∈ Finset.range (p.natDegree + 1 + 1), (p * (X - C a)).coeff i * d i := by
  have hmul : ∀ i, (p * (X - C a)).coeff i = (p * X).coeff i - a * p.coeff i := by
    intro i
    rw [mul_sub, coeff_sub, coeff_mul_C, mul_comm a]
  have h1 : ∑ i ∈ Finset.range (p.natDegree + 1 + 1), (p * X).coeff i * d i =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * d (i + 1) := by
    rw [Finset.sum_range_succ']
    simp [coeff_mul_X]
  have h2 : ∑ i ∈ Finset.range (p.natDegree + 1 + 1), a * p.coeff i * d i =
      ∑ i ∈ Finset.range (p.natDegree + 1), a * p.coeff i * d i := by
    rw [Finset.sum_range_succ, coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  simp_rw [hmul, sub_mul, Finset.sum_sub_distrib, h1, h2, mul_sub, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem natDegree_polE (κ : ℤ) (M E : ℕ) (h : E < M) : (polE κ M E).natDegree + 1 = M := by
  have hmem : E ∈ Finset.range M := Finset.mem_range.2 h
  unfold polE
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem hmem, Finset.card_range]
  omega

theorem UpperTheory.V.ZK.Cl.cBetaDiv :
    UpperTheory.V.ZK.Cl.CBetaDiv := by
  intro L F _ _ _ _ _ γ κ M E hE α 𝔡 hD P
  obtain ⟨_, hmul, hone, _, hinv, hadd, hpow⟩ := cAct L F
  have hprod : ∀ (s : Finset ℕ) (f : ℕ → Fˣ), ordP P (∏ i ∈ s, f i) = ∑ i ∈ s, ordP P (f i) := by
    intro s f
    refine Finset.induction_on s ?_ ?_
    · simpa using hpow P 1 0
    · intro j s hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj, hadd, ih]
  have key : ∀ i : ℕ, ordP P (actU (γ⁻¹ ^ i) α) =
      𝔡 (actP (γ ^ (i + 1)) P) - (κ : ℤ) ^ E * 𝔡 (actP (γ ^ i) P) := by
    intro i
    have hP : actP (γ⁻¹ ^ i) (actP (γ ^ i) P) = P := by
      rw [← hmul, inv_pow, inv_mul_cancel, hone]
    have h0 := hinv (γ⁻¹ ^ i) (actP (γ ^ i) P) α
    rw [hP] at h0
    rw [h0, hD, ← hmul, pow_succ']
    push_cast
    rfl
  have hpol : polE (κ : ℤ) M E * (X - C ((κ : ℤ) ^ E)) = pol (κ : ℤ) M := by
    rw [mul_comm]
    exact Finset.mul_prod_erase (Finset.range M) (fun j => X - C ((κ : ℤ) ^ j)) (Finset.mem_range.2 hE)
  have hs := shift_sum (polE (κ : ℤ) M E) ((κ : ℤ) ^ E) (fun i => 𝔡 (actP (γ ^ i) P))
  rw [hpol, natDegree_polE κ M E hE] at hs
  unfold polAct
  rw [hprod]
  simp only [hpow, key]
  rw [natDegree_polE κ M E hE] at *
  exact hs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlock
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

section

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] {J X : Type}

omit [NumberField L] [NumberField F] in
private theorem blk_apply {g : GG L F J} {s : J → F ≃ₐ[L] F} {β : J → X}
    {g' : ∀ x : X, ({j // β j = x} → F) ≃ₗ[F] ({j // β j = x} → F)} (h : BlockForm g s β g') (w : J → F) (x : X)
    (i : {j // β j = x}) : s i.1 (g w i.1) = g' x (fun i => s i.1 (w i.1)) i := by
  obtain ⟨j, rfl⟩ := i
  exact h w j

omit [NumberField L] [NumberField F] in
private theorem blk_glue {β : J → X} (f : ∀ x : X, ({j // β j = x} → F)) (x : X) :
    (fun i : {j // β j = x} => f (β i.1) ⟨i.1, rfl⟩) = f x := by
  funext i
  obtain ⟨j, hj⟩ := i
  subst hj
  rfl

omit [NumberField L] [NumberField F] in
private theorem blk_exists (s : J → F ≃ₐ[L] F) (β : J → X)
    (g' : ∀ x : X, ({j // β j = x} → F) ≃ₗ[F] ({j // β j = x} → F)) : ∃ g : GG L F J, BlockForm g s β g' := by
  let G : (J → F) ≃ₗ[F] (J → F) :=
    { toFun := fun v j => g' (β j) (fun i => v i.1) ⟨j, rfl⟩
      invFun := fun v j => (g' (β j)).symm (fun i => v i.1) ⟨j, rfl⟩
      map_add' := by
        intro v w
        funext j
        exact congrFun (map_add (g' (β j)) (fun i => v i.1) (fun i => w i.1)) _
      map_smul' := by
        intro c v
        funext j
        exact congrFun (map_smul (g' (β j)) c (fun i => v i.1)) _
      left_inv := by
        intro v
        funext j
        have e := blk_glue (β := β) (fun x => g' x (fun i' => v i'.1)) (β j)
        show (g' (β j)).symm (fun i : {k // β k = β j} => g' (β i.1) (fun i' => v i'.1) ⟨i.1, rfl⟩) ⟨j, rfl⟩ = v j
        rw [e, LinearEquiv.symm_apply_apply]
      right_inv := by
        intro v
        funext j
        have e := blk_glue (β := β) (fun x => (g' x).symm (fun i' => v i'.1)) (β j)
        show (g' (β j)) (fun i : {k // β k = β j} => (g' (β i.1)).symm (fun i' => v i'.1) ⟨i.1, rfl⟩) ⟨j, rfl⟩ = v j
        rw [e, LinearEquiv.apply_symm_apply] }
  let S : (J → F) ≃ₗ[L] (J → F) := LinearEquiv.piCongrRight fun j => (s j).toLinearEquiv
  refine ⟨S.trans ((G.restrictScalars L).trans S.symm), ?_⟩
  intro w j
  simp [S, G]

private theorem act_forall (σ : F ≃ₐ[L] F) (p : HeightOneSpectrum (𝓞 F) → Prop) :
    (∀ P, p (actP σ P)) ↔ ∀ P, p P := by
  constructor
  · intro h P
    obtain ⟨Q, rfl⟩ := (HeightOneSpectrum.equivOfRingEquiv
      (RingOfIntegers.mapRingEquiv σ.toRingEquiv)).surjective P
    exact h Q
  · intro h P
    exact h _

private theorem loc_iff (σ : F ≃ₐ[L] F) (b : 𝓞 L) (a : F) :
    (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → P.valuation F (σ a) ≤ 1) ↔
      ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → P.valuation F a ≤ 1 := by
  obtain ⟨hv, -, -, hm, -⟩ := cAct L F
  refine Iff.trans (act_forall σ (fun P => algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
    P.valuation F (σ a) ≤ 1)).symm ?_
  simp only [hm, hv]

private theorem lat_iff (σ : F ≃ₐ[L] F) (𝔟 𝔠 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (h : ∀ P, 𝔠 (actP σ P) = 𝔟 P) (a : F) :
    (∀ P : HeightOneSpectrum (𝓞 F), P.valuation F (σ a) ≤ WithZero.exp (-𝔠 P)) ↔
      ∀ P : HeightOneSpectrum (𝓞 F), P.valuation F a ≤ WithZero.exp (-𝔟 P) := by
  obtain ⟨hv, -⟩ := cAct L F
  refine Iff.trans (act_forall σ (fun P => P.valuation F (σ a) ≤ WithZero.exp (-𝔠 P))).symm ?_
  simp only [hv, h]

end

theorem UpperTheory.V.ZK.Cl.cBlock :
    UpperTheory.V.ZK.Cl.CBlock := by
  intro L F _ _ _ _ _ J X s β g'
  refine ⟨blk_exists s β g', fun g hg => ⟨?_, ?_, ?_⟩⟩
  · have hg' : ∀ (w : J → F) (j : J), s j (g w j) = g' (β j) (fun i => s i.1 (w i.1)) ⟨j, rfl⟩ := hg
    intro u u' hu
    have hu' : ∀ k, s k (u k : F) = (u' (β k) : F) := fun k => by
      have := congrArg Units.val (hu k)
      simpa [UpperTheory.V.ZK.actU] using this
    show g * diag L u = diag L u * g
    refine LinearEquiv.ext fun w => funext fun j => ?_
    show g (diag L u w) j = diag L u (g w) j
    have hw : diag L u w = fun k => (u k : F) * w k := funext (diag_apply u w)
    rw [hw, diag_apply]
    apply (s j).injective
    rw [hg', map_mul, hg', hu']
    have e : (fun i : {k // β k = β j} => s i.1 ((u i.1 : F) * w i.1)) =
        (u' (β j) : F) • (fun i => s i.1 (w i.1)) := by
      funext i
      obtain ⟨k, hk⟩ := i
      simp only [map_mul, hu', Pi.smul_apply, smul_eq_mul, hk]
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul]
  · classical
    have hg' : ∀ (w : J → F) (j : J), s j (g w j) = g' (β j) (fun i => s i.1 (w i.1)) ⟨j, rfl⟩ := hg
    intro b hb x w
    have hb' : ∀ W : J → F, InLoc b W ↔ InLoc b (g W) := hb
    let W : J → F := fun j => if h : β j = x then (s j).symm (w ⟨j, h⟩) else 0
    have hW : (fun i : {k // β k = x} => s i.1 (W i.1)) = w := by
      funext i
      obtain ⟨k, hk⟩ := i
      subst hk
      simp [W]
    have hW0 : ∀ j, β j ≠ x → W j = 0 := by
      intro j hj
      simp [W, hj]
    have h0 : ∀ j, β j ≠ x → g W j = 0 := by
      intro j hj
      apply (s j).injective
      rw [hg', map_zero]
      have hz : (fun i : {k // β k = β j} => s i.1 (W i.1)) = 0 := by
        funext i
        obtain ⟨k, hk⟩ := i
        have hk' : β k ≠ x := hk ▸ hj
        simp [hW0 k hk']
      rw [hz, map_zero]
      rfl
    have key : ∀ V : J → F, (∀ j, β j ≠ x → V j = 0) →
        (InLoc b V ↔ InLoc b (fun i : {k // β k = x} => s i.1 (V i.1))) := by
      intro V hV
      constructor
      · intro h i P hP
        exact (loc_iff (s i.1) b (V i.1)).2 (h i.1) P hP
      · intro h j P hP
        by_cases hj : β j = x
        · exact (loc_iff (s j) b (V j)).1 (h ⟨j, hj⟩) P hP
        · rw [hV j hj, map_zero]
          exact zero_le'
    have hgW : (fun i : {k // β k = x} => s i.1 (g W i.1)) = g' x w := by
      funext i
      rw [blk_apply hg W x i, hW]
    have := (key W hW0).symm.trans ((hb' W).trans (key (g W) h0))
    rw [hW, hgW] at this
    exact this
  · have hg' : ∀ (w : J → F) (j : J), s j (g w j) = g' (β j) (fun i => s i.1 (w i.1)) ⟨j, rfl⟩ := hg
    intro 𝔟 𝔠 h𝔠 hblk w
    constructor
    · intro hw j P
      apply (lat_iff (s j) (𝔟 j) (𝔠 j) (h𝔠 j) (g w j)).1 ?_ P
      intro Q
      rw [hg']
      have h2 : InLat 0 (fun i : {k // β k = β j} => s i.1 (w i.1)) := by
        intro i Q'
        exact (lat_iff (s i.1) 0 0 (fun _ => rfl) (w i.1)).2 (hw i.1) Q'
      exact (hblk (β j) _).1 h2 ⟨j, rfl⟩ Q
    · intro hw j P
      apply (lat_iff (s j) 0 0 (fun _ => rfl) (w j)).1 ?_ P
      intro Q
      have h2 : InLat (fun i : {k // β k = β j} => 𝔠 i.1) (g' (β j) (fun i => s i.1 (w i.1))) := by
        intro i Q'
        rw [← blk_apply hg w (β j) i]
        exact (lat_iff (s i.1) (𝔟 i.1) (𝔠 i.1) (h𝔠 i.1) (g w i.1)).2 (hw i.1) Q'
      exact (hblk (β j) _).2 h2 ⟨j, rfl⟩ Q
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CMu
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cMu :
    UpperTheory.V.ZK.Cl.CMu := by
  intro L F _ _ _ _ _ J _ k _ r b hb hsurj hsplit
  classical
  obtain ⟨cU, cAM, cA, cLoc⟩ := cRes L F k r
  obtain ⟨aV, aMul, aOne, aMem, -, -, -⟩ := cAct L F
  obtain ⟨hs1, hs2⟩ := hsplit
  have cL := (cLoc b hb).1
  have vInt : ∀ (P : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F), HeightOneSpectrum.valuation F P (a : F) ≤ 1 :=
    fun P a => P.valuation_le_one a
  have R0 : ResF r (0 : F) 0 := by simpa using cAM 0
  have Rsub : ∀ (x y : F) (u w : k), ResF r x u → ResF r y w → ResF r (x - y) (u - w) := by
    intro x y u w hx hy
    have h2 := (cA _ _ _ _ hx (cA _ _ _ _ (cAM (-1)) hy).2).1
    have e1 : ((-1 : 𝓞 F) : F) = -1 := by simp
    rw [e1, map_neg, map_one] at h2
    simpa [sub_eq_add_neg] using h2
  have Runiq : ∀ (x : J → F) (v w : Gal(F/L) × J → k), RedV L r x v → RedV L r x w → v = w := by
    intro x v w hv hw
    funext p
    exact cU _ _ _ (hv p.1 p.2) (hw p.1 p.2)
  have L0 : ∀ x : J → F, InLoc b x → ∀ (σ : Gal(F/L)) (j : J), ∃ u, ResF r (σ (x j)) u := by
    intro x hx σ j
    refine (cL (σ (x j)) ?_).2
    intro P hP
    have e : actP σ (actP σ⁻¹ P) = P := by rw [← aMul, mul_inv_cancel, aOne]
    rw [← e, aV]
    exact hx j _ (fun hm => hP ((aMem σ⁻¹ P b).1 hm))
  have Iadd : ∀ x y : J → F, InLoc b x → InLoc b y → InLoc b (x + y) := by
    intro x y hx hy j P hP
    exact le_trans (Valuation.map_add _ _ _) (max_le (hx j P hP) (hy j P hP))
  have Isub : ∀ x y : J → F, InLoc b x → InLoc b y → InLoc b (x - y) := by
    intro x y hx hy j P hP
    exact le_trans (Valuation.map_sub _ _ _) (max_le (hx j P hP) (hy j P hP))
  have Ismul : ∀ (m : 𝓞 L) (x : J → F), InLoc b x → InLoc b ((m : L) • x) := by
    intro m x hx j P hP
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact mul_le_one' (vInt P (algebraMap (𝓞 L) (𝓞 F) m)) (hx j P hP)
  have GI : ∀ (g : GLoc F J b) (x : J → F), InLoc b x → InLoc b ((g : GG L F J) x) := by
    intro g x hx
    have hg : ∀ z : J → F, InLoc b z ↔ InLoc b ((g : GG L F J) z) := g.2
    exact (hg x).1 hx
  have L1 : ∀ v : Gal(F/L) × J → k, ∃ x : J → F, InLoc b x ∧ RedV L r x v := by
    intro v
    choose a ha using fun j => hs1 (fun σ => v (σ, j))
    refine ⟨fun j => (a j : F), fun j P _ => vInt P (a j), ?_⟩
    intro σ j
    have h := cAM (actO σ (a j))
    rw [ha j σ] at h
    exact h
  have Kz : ∀ (g : GLoc F J b) (y : J → F), InLoc b y → RedV L r y 0 → RedV L r ((g : GG L F J) y) 0 := by
    intro g y hy hy0
    let W : Set (J → F) := {z | RedV L r ((g : GG L F J) z) 0}
    have W0 : (0 : J → F) ∈ W := by
      intro σ j
      show ResF r (σ (((g : GG L F J) 0) j)) 0
      rw [map_zero, Pi.zero_apply, map_zero]
      exact R0
    have Wadd : ∀ z1 z2, z1 ∈ W → z2 ∈ W → z1 + z2 ∈ W := by
      intro z1 z2 h1 h2 σ j
      have := (cA _ _ _ _ (h1 σ j) (h2 σ j)).1
      show ResF r (σ (((g : GG L F J) (z1 + z2)) j)) 0
      rw [map_add (f := _), Pi.add_apply, map_add (f := _)]
      simpa using this
    have Wgen : ∀ (j : J) (c : F), (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
        HeightOneSpectrum.valuation F P c ≤ 1) →
        ∀ m : 𝓞 L, r (algebraMap (𝓞 L) (𝓞 F) m) = 0 → Pi.single j (c * algebraMap L F (m : L)) ∈ W := by
      intro j c hc m hm
      have hs : InLoc b (Pi.single j c : J → F) := by
        intro i P hP
        by_cases hij : i = j
        · subst hij
          simpa using hc P hP
        · simp [Pi.single_apply, hij]
      have e : (Pi.single j (c * algebraMap L F (m : L)) : J → F) = (m : L) • (Pi.single j c : J → F) := by
        ext i
        by_cases hij : i = j
        · subst hij
          simp [Algebra.smul_def, mul_comm]
        · simp [Pi.single_apply, hij]
      intro σ j'
      show ResF r (σ (((g : GG L F J) (Pi.single j (c * algebraMap L F (m : L)))) j')) 0
      rw [e, map_smul, Pi.smul_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      obtain ⟨u, hu⟩ := L0 _ (GI g _ hs) σ j'
      have := (cA _ _ _ _ (cAM (algebraMap (𝓞 L) (𝓞 F) m)) hu).2
      rw [hm, zero_mul] at this
      exact this
    have Wspan : ∀ a ∈ Ideal.map (algebraMap (𝓞 L) (𝓞 F)) (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))),
        ∀ (j : J) (c : F), (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
          HeightOneSpectrum.valuation F P c ≤ 1) → Pi.single j (c * (a : F)) ∈ W := by
      intro a ha
      replace ha : a ∈ Submodule.span (𝓞 F)
          (⇑(algebraMap (𝓞 L) (𝓞 F)) '' (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F))))) := ha
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, hm, rfl⟩ := hx
        intro j c hc
        exact Wgen j c hc m (RingHom.mem_ker.1 hm)
      | zero =>
        intro j c hc
        simpa using W0
      | add x y _ _ hx hy =>
        intro j c hc
        have := Wadd _ _ (hx j c hc) (hy j c hc)
        simpa [mul_add, Pi.single_add] using this
      | smul c' x _ hx =>
        intro j c hc
        have := hx j (c * (c' : F)) (fun P hP => by
          rw [map_mul]
          exact mul_le_one' (hc P hP) (vInt P c'))
        simpa [mul_assoc] using this
    have hyW : ∀ j, Pi.single j (y j) ∈ W := by
      intro j
      obtain ⟨⟨n, a, hna⟩, -⟩ := cL (y j) (fun P hP => hy j P hP)
      have eβ : algebraMap (𝓞 L) F b = algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b) := rfl
      rw [eβ] at hna
      have hβ0 : algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 := by
        intro h0
        apply hb
        rw [IsFractionRing.injective (𝓞 F) F (h0.trans (map_zero _).symm), map_zero]
      have hmem : a ∈ Ideal.map (algebraMap (𝓞 L) (𝓞 F)) (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))) := by
        apply hs2
        intro σ
        have h1 := cAM (actO σ a)
        have h2 : ResF r (σ (a : F)) (r (algebraMap (𝓞 L) (𝓞 F) b) ^ n * 0) := by
          rw [← hna, map_mul, map_pow]
          have hb' : σ (algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b)) =
              algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b) := AlgEquiv.commutes σ (b : L)
          rw [hb']
          have hbn := cAM (algebraMap (𝓞 L) (𝓞 F) b ^ n)
          rw [map_pow] at hbn
          have hbn' : ResF r (algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b) ^ n)
              (r (algebraMap (𝓞 L) (𝓞 F) b) ^ n) := by
            simpa using hbn
          exact (cA _ _ _ _ hbn' (hy0 σ j)).2
        rw [mul_zero] at h2
        exact cU _ _ _ h1 h2
      have hyj : y j = ((algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b)) ^ n)⁻¹ * (a : F) := by
        rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero n hβ0)]
        exact hna
      have hc : ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
          HeightOneSpectrum.valuation F P (((algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b)) ^ n)⁻¹) ≤ 1 := by
        intro P hP
        have h1 : HeightOneSpectrum.valuation F P (algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b)) = 1 := by
          rw [P.valuation_of_algebraMap]
          exact le_antisymm (P.intValuation_le_one _)
            (not_lt.1 (fun h => hP ((P.intValuation_lt_one_iff_mem _).1 h)))
        rw [map_inv₀, map_pow, h1, one_pow, inv_one]
      rw [hyj]
      exact Wspan a hmem j _ hc
    have hyW' : y ∈ W := by
      rw [← Finset.univ_sum_single y]
      exact Finset.sum_induction _ (· ∈ W) (fun a b ha hb => Wadd a b ha hb) W0 (fun j _ => hyW j)
    exact hyW'
  choose lf hlfI hlfR using L1
  let rd : (J → F) → (Gal(F/L) × J → k) := fun x p =>
    if h : ∃ u, ResF r (p.1 (x p.2)) u then h.choose else 0
  have P1 : ∀ x, InLoc b x → RedV L r x (rd x) := by
    intro x hx σ j
    have h := L0 x hx σ j
    show ResF r (σ (x j)) (if h : ∃ u, ResF r (σ (x j)) u then h.choose else 0)
    rw [dite_eq_left h]
    exact h.choose_spec
  let T : GLoc F J b → (Gal(F/L) × J → k) → (Gal(F/L) × J → k) := fun g v => rd ((g : GG L F J) (lf v))
  have P3 : ∀ (g : GLoc F J b) (x : J → F) (v : Gal(F/L) × J → k), InLoc b x → RedV L r x v →
      RedV L r ((g : GG L F J) x) (T g v) := by
    intro g x v hx hv
    have hd : RedV L r (x - lf v) 0 := by
      intro σ j
      have := Rsub _ _ _ _ (hv σ j) (hlfR v σ j)
      rw [sub_self] at this
      simpa using this
    have hK := Kz g _ (Isub _ _ hx (hlfI v)) hd
    have hP1 := P1 _ (GI g _ (hlfI v))
    intro σ j
    have := (cA _ _ _ _ (hK σ j) (hP1 σ j)).1
    rw [map_sub, Pi.sub_apply, map_sub, sub_add_cancel] at this
    simpa using this
  have Tadd : ∀ (g : GLoc F J b) v w, T g (v + w) = T g v + T g w := by
    intro g v w
    have h1 := P3 g (lf v + lf w) (v + w) (Iadd _ _ (hlfI v) (hlfI w)) (fun σ j => by
      have := (cA _ _ _ _ (hlfR v σ j) (hlfR w σ j)).1
      simpa using this)
    have h2 : RedV L r ((g : GG L F J) (lf v + lf w)) (T g v + T g w) := by
      intro σ j
      have := (cA _ _ _ _ (P1 _ (GI g _ (hlfI v)) σ j) (P1 _ (GI g _ (hlfI w)) σ j)).1
      rw [map_add (f := _), Pi.add_apply, map_add (f := _)]
      exact this
    exact Runiq _ _ _ h1 h2
  have Tsmul : ∀ (g : GLoc F J b) (c : k) v, T g (c • v) = c • T g v := by
    intro g c v
    obtain ⟨m, hm⟩ := hsurj c
    have hm' : r (algebraMap (𝓞 L) (𝓞 F) m) = c := hm
    have h1 := P3 g _ (c • v) (Ismul m _ (hlfI v)) (fun σ j => by
      have := (cA _ _ _ _ (cAM (algebraMap (𝓞 L) (𝓞 F) m)) (hlfR v σ j)).2
      rw [hm'] at this
      show ResF r (σ (((m : L) • lf v) j)) (c * v (σ, j))
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      exact this)
    have h2 : RedV L r ((g : GG L F J) ((m : L) • lf v)) (c • T g v) := by
      intro σ j
      have := (cA _ _ _ _ (cAM (algebraMap (𝓞 L) (𝓞 F) m)) (P1 _ (GI g _ (hlfI v)) σ j)).2
      rw [hm'] at this
      show ResF r (σ (((g : GG L F J) ((m : L) • lf v)) j)) (c * T g v (σ, j))
      rw [map_smul, Pi.smul_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      exact this
    exact Runiq _ _ _ h1 h2
  have Tmul : ∀ (g h : GLoc F J b) v, T (g * h) v = T g (T h v) := by
    intro g h v
    have h1 := P1 _ (GI (g * h) _ (hlfI v))
    have h2 := P3 g _ (T h v) (GI h _ (hlfI v)) (P1 _ (GI h _ (hlfI v)))
    exact Runiq _ _ _ h1 h2
  have Tone : ∀ v, T 1 v = v := by
    intro v
    exact Runiq _ _ _ (P1 _ (GI 1 _ (hlfI v))) (hlfR v)
  let Tl : GLoc F J b → ((Gal(F/L) × J → k) →ₗ[k] (Gal(F/L) × J → k)) := fun g =>
    { toFun := T g
      map_add' := Tadd g
      map_smul' := fun c v => Tsmul g c v }
  refine ⟨{ toFun := fun g => LinearEquiv.ofLinear (Tl g) (Tl g⁻¹)
              (LinearMap.ext fun v => by
                show T g (T g⁻¹ v) = v
                rw [← Tmul, mul_inv_cancel, Tone])
              (LinearMap.ext fun v => by
                show T g⁻¹ (T g v) = v
                rw [← Tmul, inv_mul_cancel, Tone])
            map_one' := LinearEquiv.ext fun v => Tone v
            map_mul' := fun g h => LinearEquiv.ext fun v => Tmul g h v }, ?_⟩
  intro g x v hx hv
  exact P3 g x v hx hv
end

