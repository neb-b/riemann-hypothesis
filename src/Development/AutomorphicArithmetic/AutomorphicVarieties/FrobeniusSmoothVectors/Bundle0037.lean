module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0005
public import Mathlib.RingTheory.Teichmuller
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0035
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0036

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScCong
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_cong :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (u : c.Oˣ) (a : (Qbar l)ˣ), ‖a.val - u.val.1‖ < 1 → Sd.Cong (a ^ 2) 1 → Units.map (residue c.O).toMonoidHom u ^ 2 = 1 := by
  intro l _ c u a ha hcong
  have hu := (sc_norm l c u.val).1
  unfold Sd.Cong at hcong
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hcong
  set x : PadicAlgCl l := ((u.val : c.O) : PadicAlgCl l) with hx
  set y : PadicAlgCl l := a.val with hy
  have hy1 : ‖y‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (y - x) x
    rw [sub_add_cancel] at h
    exact h.trans (max_le ha.le hu)
  have hxy : ‖x + y‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hu hy1)
  have hmem : (u.val ^ 2 - 1 : c.O) ∈ maximalIdeal c.O := by
    rw [(sc_norm l c _).2]
    have e : ((u.val ^ 2 - 1 : c.O) : PadicAlgCl l) = (x - y) * (x + y) + (y ^ 2 - 1) := by
      rw [hx]
      push_cast
      ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hcong)
    rw [norm_mul]
    have : ‖x - y‖ < 1 := by rw [← norm_neg, neg_sub]; exact ha
    nlinarith [norm_nonneg (x - y), norm_nonneg (x + y)]
  ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one]
  rw [← sub_eq_zero]
  have h0 := (residue_eq_zero_iff _).2 hmem
  rw [map_sub, map_pow, map_one] at h0
  exact h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScTeich
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := ‹CharP (ResidueField O) l›
  haveI hp : PerfectRing (ResidueField O) l := inferInstance
  haveI : PerfectRing (O ⧸ maximalIdeal O) l := hp
  let f : (O ⧸ maximalIdeal O) →* O := (Perfection.teichmuller l (maximalIdeal O)).comp
    (Perfection.liftMonoidHom l (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) (MonoidHom.id _))
  refine ⟨f, fun x => ?_⟩
  have h := Perfection.mk_teichmuller (p := l) (I := maximalIdeal O)
    (Perfection.liftMonoidHom l (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) (MonoidHom.id _) x)
  exact h.trans (Perfection.coeffMonoidHom_zero_liftMonoidHom l (MonoidHom.id _) x)

theorem UpperTheory.V.Fr.sc_teich :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l], Finite (ResidueField c.O) → ∃ T : (ResidueField c.O)ˣ →* (Qbar l)ˣ, Function.Injective T ∧ ∀ (u : c.Oˣ) (j : ℕ) (s : G ℚ Ω), ‖(GlobalTheory.GalOfCusp.cycBar ℚ Ω l s ^ j * T (Units.map (residue c.O).toMonoidHom u * (omO Ω l c.O s ^ j)⁻¹)).val - u.val.1‖ < 1 := by
  intro Ω _ _ _ l _ c _ hfin
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (dvrFacts l c.O).2.2.2.1
  obtain ⟨τ, hτ⟩ := teich_ex l c.O
  let ι : c.O →* Qbar l := c.O.val.toRingHom.toMonoidHom
  refine ⟨Units.map (ι.comp τ), ?_, ?_⟩
  · intro x y hxy
    have h1 : ((Units.map (ι.comp τ) x).val) = (Units.map (ι.comp τ) y).val := by rw [hxy]
    have h2 : τ x.val = τ y.val := Subtype.ext h1
    apply Units.ext
    rw [← hτ x.val, ← hτ y.val, h2]
  · intro u j s
    have hω : ((omO Ω l c.O s).val : ResidueField c.O) = residue c.O (chiO ℚ Ω l c.O s).val :=
      (UpperTheory.V.X.cycKFacts Ω l (ResidueField c.O)).2 c (residue c.O) s
    have hc : (GlobalTheory.GalOfCusp.cycBar ℚ Ω l s).val = ((chiO ℚ Ω l c.O s).val : PadicAlgCl l) := rfl
    set w : (ResidueField c.O)ˣ := Units.map (residue c.O).toMonoidHom u * (omO Ω l c.O s ^ j)⁻¹
    have key : (chiO ℚ Ω l c.O s).val ^ j * τ w.val - u.val ∈ maximalIdeal c.O := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residue c.O _ = 0
      rw [map_sub, map_mul, map_pow, hτ, ← hω]
      simp only [w, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.coe_map, MonoidHom.coe_coe]
      have hne : ((omO Ω l c.O s).val : ResidueField c.O) ^ j ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
      rw [mul_left_comm, mul_inv_cancel₀ hne, mul_one]
      exact sub_self _
    have hn := ((sc_norm l c _).2.1 key)
    convert hn using 2
    simp [Units.val_mul, Units.val_pow_eq_pow_val, hc, ι]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScTheta
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_theta :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → w ≡ 1 [MOD l] → ∃ θ : G ℚ Ω →* (Qbar l)ˣ, θ.ker = Hth Ω l w ∧ θ ≠ 1 ∧ θ ^ l = 1 ∧ Af.KillsMu w θ := by
  intro Ω _ _ _ l _ w hw hwl
  obtain ⟨-, hc, hidx, -, -⟩ := hth Ω l w hw hwl
  haveI hN : (Hth Ω l w).Normal := ⟨fun n hn g => by
    have h0 := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
    rw [commutatorElement_def] at h0
    have h1 := hc h0
    have h2 : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by group
    rw [h2]
    exact (Hth Ω l w).mul_mem h1 hn⟩
  have hcardQ : Nat.card (G ℚ Ω ⧸ Hth Ω l w) = l := hidx
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) l
  have hcardR : Nat.card (rootsOfUnity l (Qbar l)) = l := hζ.card_rootsOfUnity
  let e := mulEquivOfPrimeCardEq hcardQ hcardR
  let θ : G ℚ Ω →* (Qbar l)ˣ :=
    (rootsOfUnity l (Qbar l)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Hth Ω l w)))
  have hθ : ∀ s, θ s = ((e (QuotientGroup.mk' (Hth Ω l w) s) : rootsOfUnity l (Qbar l)) : (Qbar l)ˣ) :=
    fun s => rfl
  have hker : θ.ker = Hth Ω l w := by
    ext s
    rw [MonoidHom.mem_ker, hθ]
    constructor
    · intro h
      have h' : e (QuotientGroup.mk' (Hth Ω l w) s) = 1 := Subtype.ext h
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
      exact h'
    · intro h
      have h' : QuotientGroup.mk' (Hth Ω l w) s = 1 := (QuotientGroup.eq_one_iff s).mpr h
      rw [h', map_one]
      rfl
  refine ⟨θ, hker, ?_, ?_, ?_⟩
  · intro h1
    have htop : Hth Ω l w = ⊤ := by rw [← hker, h1, MonoidHom.ker_one]
    rw [htop, Subgroup.index_top] at hidx
    exact (Fact.out : l.Prime).one_lt.ne hidx
  · ext s
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, hθ]
    exact congrArg Units.val ((mem_rootsOfUnity _ _).mp (e (QuotientGroup.mk' (Hth Ω l w) s)).2)
  · unfold Af.KillsMu
    intro s hs
    rw [← MonoidHom.mem_ker, hker]
    unfold Hth
    refine ⟨⟨1, fun z hz => ?_⟩, ⟨1, fun z hz => ?_⟩⟩
    · rw [one_pow, pow_one]
      exact hs z hz
    · rw [one_pow, pow_one]
      have e1 := congrArg (s⁻¹ : G ℚ Ω) (hs z hz)
      rw [← e1]
      simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StSel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem toGS_eq_one_of_mem_inertia_of_notMem (Ω : Type) [Field Ω] [CharZero Ω] (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ S) (A : ValuationSubring Ω) (hA : IsPlaceOver A v)
    (s : G ℚ Ω) (hs : s ∈ Ine (F := ℚ) A) : toGS Ω S s = 1 := by
  unfold toGS
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  unfold ReciprocityTheory.Gal.NS
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff]
  exact ⟨v, hv, A, hA, hs⟩

private theorem continuous_toGS' (Ω : Type) [Field Ω] [CharZero Ω] (S : Set (HeightOneSpectrum (𝓞 ℚ))) :
    Continuous (toGS Ω S) := by
  unfold toGS
  exact continuous_quot_mk

private theorem toGS_surjective' (Ω : Type) [Field Ω] [CharZero Ω] (S : Set (HeightOneSpectrum (𝓞 ℚ))) :
    Function.Surjective (toGS Ω S) := by
  unfold toGS
  exact QuotientGroup.mk'_surjective _

set_option maxHeartbeats 200000 in
theorem UpperTheory.V.Fr.st_sel :
    GC.Hypotheses₂ → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (κ : G ℚ Ω →* kˣ), IsOpen (κ.ker : Set (G ℚ Ω)) → (∃ σ : G ℚ Ω, IsCC σ ∧ κ σ ≠ 1) → (∃ s, κ s ≠ GC.cycF ℚ Ω l k s) → ∀ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ContainsAbove S l → (∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := ℚ) A ≤ κ.ker) → ∀ v₀ ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ v₀.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A v₀ → Dec (F := ℚ) A ≤ κ.ker ⊓ (GC.cycF ℚ Ω l k).ker) → (∀ v ∈ S, v ≠ v₀ → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∃ s ∈ Dec (F := ℚ) A, κ s ≠ 1) → ∃ y : G ℚ Ω → k, IsLocallyConstant y ∧ (∀ s t, y (s * t) = y s + κ s * y t) ∧ (¬ ∃ b, ∀ s, y s = κ s * b - b) ∧ (∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ s ∈ Ine (F := ℚ) A, y s = 0) ∧ ∀ v ∈ S, v ≠ v₀ → ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ ∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = κ s * b - b := by
  intro hP Ω _ _ _ l _ hl2 k _ _ _ κ hκo hCC hs0ex S hSA hIne v₀ hv₀ hlv₀ hD0 hDo
  obtain ⟨σ, hσ, hσκ⟩ := hCC
  obtain ⟨s0, hs0⟩ := hs0ex
  have hdvd : l ∣ l ^ 1 := by simp
  haveI : Fact (l ^ 1).Prime := ⟨by simpa using (Fact.out : l.Prime)⟩
  letI alg : Algebra (ZMod (l ^ 1)) k := (ZMod.castHom hdvd k).toAlgebra
  letI : TopologicalSpace k := ⊥
  haveI : DiscreteTopology k := ⟨rfl⟩
  obtain ⟨κS, hκS, hκSlc⟩ := st_desc Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) kˣ κ hκo
    (fun v hv A hA => hIne v hv A hA)
  have hκS' : ∀ g, κS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g) = κ g := fun g => by
    rw [← MonoidHom.comp_apply, hκS]
  let ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) k :=
    (Algebra.lmul (ZMod (l ^ 1)) k).toRingHom.toMonoidHom.comp ((Units.coeHom k).comp κS)
  have hρ : ∀ g m, ρ g m = (κS g : k) * m := fun g m => rfl
  have hcont : ReciprocityTheory.Gal.ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    have hc : Continuous fun g => (κS g : k) :=
      (hκSlc.comp (fun u : kˣ => (u : k))).continuous
    exact (hc.comp continuous_fst).mul continuous_snd
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := 1) hSA
  let Av : S → ValuationSubring Ω := fun v => (exists_isPlaceOver Ω v.1).choose
  have hAv : ∀ v : S, IsPlaceOver (Av v) v.1 := fun v => (exists_isPlaceOver Ω v.1).choose_spec
  have kill : ∀ (a : kˣ) (m : k), a ≠ 1 → (a : k) * m = m → m = 0 := by
    intro a m ha hm
    have h2 : ((a : k) - 1) * m = 0 := by rw [sub_mul, one_mul, hm, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (fun h => ha (Units.val_eq_one.mp h)))
  have hfix : ∀ m : k, ρ (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) σ) m = m → m = 0 := by
    intro m hm
    rw [hρ, hκS'] at hm
    exact kill _ m hσκ hm
  have hdual : H0 (twDual μ ρ) = ⊥ := by
    refine st_dual l k _ μ ρ (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) s0) (κ s0 : k) (fun m => by rw [hρ, hκS']) ?_
    intro h
    apply hs0
    apply Units.ext
    have hμs : μ (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) s0) = cycMod ℚ Ω l 1 s0 := by
      rw [← MonoidHom.comp_apply, hμ]
    rw [h, hμs]
    rfl
  have hother : ∀ v : S, v ≠ ⟨v₀, hv₀⟩ → H0 (MonoidHom.comp ρ (locFam S Av v)) = ⊥ := by
    intro v hv
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, Submodule.mem_bot]
    constructor
    · intro hm
      obtain ⟨s, hs, hκs⟩ := hDo v.1 v.2 (fun h => hv (Subtype.ext h)) (Av v) (hAv v)
      have h1 := hm ⟨s, hs⟩
      change (κS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) s) : k) * m = m at h1
      rw [hκS'] at h1
      exact kill _ m hκs h1
    · rintro rfl g
      exact map_zero _
  have hloc : Nat.card (H0 (MonoidHom.comp ρ (locFam S Av ⟨v₀, hv₀⟩))) <
      Nat.card (H1 (MonoidHom.comp ρ (locFam S Av ⟨v₀, hv₀⟩))) := by
    refine st_loc hP.1.lf hP.1.lt hP.1.le Ω l k (Av ⟨v₀, hv₀⟩) v₀ (hAv ⟨v₀, hv₀⟩) hlv₀ ?_ _ ?_
    · intro g hg
      have h1 : GC.cycF ℚ Ω l k g = 1 := (hD0 (Av ⟨v₀, hv₀⟩) (hAv ⟨v₀, hv₀⟩) hg).2
      apply Units.ext
      apply (ZMod.castHom hdvd k).injective
      have h2 := congrArg Units.val h1
      rw [Units.val_one, map_one]
      exact h2
    · intro g m
      change (κS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g.1) : k) * m = m
      have h1 : κ g.1 = 1 := (hD0 (Av ⟨v₀, hv₀⟩) (hAv ⟨v₀, hv₀⟩) g.2).1
      rw [hκS', h1, Units.val_one, one_mul]
  obtain ⟨z, hz, hzB, hzloc⟩ := st_count hP.1.gf hP.gw Ω l hl2 k S ρ hSA hcont μ hμ Av hAv σ hσ hfix
    hdual ⟨v₀, hv₀⟩ hother hloc
  rw [mem_Z1_iff_cocycle] at hz
  obtain ⟨hzc, hzco⟩ := hz
  have hz1 : z 1 = 0 := by
    have h1 := hzco 1 1
    rw [mul_one, hρ, map_one, Units.val_one, one_mul] at h1
    linear_combination (-1 : k) * h1
  refine ⟨fun s => z (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) s), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((IsLocallyConstant.iff_continuous z).2 hzc).comp_continuous (continuous_toGS' Ω _)
  · intro s t
    simp only [map_mul]
    rw [hzco, hρ, hκS']
  · rintro ⟨b, hb⟩
    apply hzB
    rw [mem_coboundaries1]
    refine ⟨b, fun g => ?_⟩
    obtain ⟨s, rfl⟩ := toGS_surjective' Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g
    have hbs := hb s
    beta_reduce at hbs
    rw [hbs, hρ, hκS']
  · intro v hv A hA s hs
    simp only
    rw [toGS_eq_one_of_mem_inertia_of_notMem Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) v hv A hA s hs, hz1]
  · intro v hv hne
    obtain ⟨m, hm⟩ := hzloc ⟨v, hv⟩ (fun h => hne (congrArg Subtype.val h))
    exact ⟨Av ⟨v, hv⟩, hAv _, m, fun s hs => by
      beta_reduce
      rw [hm s hs, hρ, hκS']⟩
end

