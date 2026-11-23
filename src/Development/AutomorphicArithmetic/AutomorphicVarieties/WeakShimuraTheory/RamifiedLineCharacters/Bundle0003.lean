module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupRaw
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupRaw :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → Φ.Ok a → ∀ 𝒩 : Set Γ → Prop, Φ.Gys l 𝒩 → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ N', 𝒩 N' ∧ ∃ (x : Γ → k) (m : Φ.ι → k), (Φ.wN N').Coc a w x ∧ Φ.LocTriv a w x m ∧ (∃ g, a (Φ.rt w g) = 1 ∧ x g ≠ 0) ∧
        ∀ j, ∃ z, (Φ.wN N').Cup a w w' x (y j) z m := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ hfin hok 𝒩 hG w w' J _ y hy
  obtain ⟨M, i1, i2, i3, i4, i5, ρ, p, q, m0, hc, hN, hp, hq, hm0, hpm⟩ :=
    Gys.extRep Φ a l hfin hok.lc w w' J y hy
  obtain ⟨N', hN', c, hcZ, hc0, hloc, g, hg1, hcg, hspan⟩ :=
    hG M ρ hc (fun g hg => hN g (hok.kill g hg) (fun j => (hy j).kill g hg)) m0 hm0
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle ρ c).1 hcZ
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hcont
  have hrt : ∀ u, (Φ.wN N').rt u = Φ.rt u := fun u => rfl
  choose mm hmm using hloc
  have hpg : p (c g) ≠ 0 := hpm _ hspan hcg
  refine ⟨N', hN', fun s => p (c s), fun v => -p (mm v), ?_, ?_, ?_, ?_⟩
  · refine ⟨hlc.comp p, ?_, ?_⟩
    · intro s t
      rw [hrt, hcoc, map_add (f := _), hp]
    · intro s hs
      simp [hc0 s hs]
  · intro v s hs
    show p (c s) = -p (mm v) - a ↑((Φ.rt w) s) * -p (mm v)
    rw [hmm v s hs, map_sub, hp]
    ring
  · refine ⟨g, ?_, hpg⟩
    have h := hp g (c g)
    rw [hg1] at h
    change p (c g) = _ at h
    have h2 : (a ↑((Φ.rt w) g) - 1) * p (c g) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hpg
  · intro j
    refine ⟨fun s => q j (c s), hlc.comp (q j), ?_, ?_, ?_⟩
    · intro s t
      simp only [hrt]
      rw [hcoc, map_add (f := _), hq]
      ring
    · intro s hs
      simp [hc0 s hs]
    · intro v
      refine ⟨-q j (mm v), fun s hs => ?_⟩
      simp only [hrt]
      rw [hmm v s hs, map_sub, hq]
      ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GwLower
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.gwLower :
    GlobalFiniteness → GreenbergWiles → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContainsAbove S l → ContAction ρ →
      ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond ρ (locFam S Av),
        ∏ v : S, Nat.card (L v) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ Module.finrank ℚ F) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by
  classical
  intro hGF hGW F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl S ρ hS hρ Av hA L
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := 1) (S := S) hS
  obtain ⟨c, hc⟩ := UpperTheory.V.Ws.Gys.ccEx F Ω
  have e := hGW F Ω l 1 M S ρ one_pos hl hS hρ μ hμ Av hA c hc L
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI hfd : Finite (TDual (ZMod (l ^ 1)) M) := DFunLike.finite _
  haveI hf1 : Finite (H1 ρ) := (hGF F Ω l 1 M S ρ one_pos hS hρ).2.1
  have hM : 0 < Nat.card M := Nat.card_pos
  have p1 : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have p2 : 0 < Nat.card (H0 (twDual μ ρ)) := Nat.card_pos
  have p3 : 0 < ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have p4 : 0 < archH0Card S ρ c := by
    unfold archH0Card
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (pow_pos hM _)
    haveI : Nonempty {m : M // ρ (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  have b2 : Nat.card (H0 (twDual μ ρ)) ≤ Nat.card (TDual (ZMod (l ^ 1)) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have b4 : archH0Card S ρ c ≤ Nat.card M ^ Module.finrank ℚ F := by
    unfold archH0Card
    have h1 : (∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
        Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) ≤ Nat.card M ^ InfinitePlace.nrRealPlaces F := by
      have h2 := Finset.prod_le_pow_card (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal))
        (fun w => Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) (Nat.card M)
        (fun w _ => Nat.card_le_card_of_injective _ Subtype.val_injective)
      have h3 : (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal)).card = InfinitePlace.nrRealPlaces F := by
        rw [InfinitePlace.nrRealPlaces, Fintype.card_subtype]
      rwa [h3] at h2
    refine (Nat.mul_le_mul_right _ h1).trans ?_
    rw [← pow_add]
    refine Nat.pow_le_pow_right hM ?_
    have := InfinitePlace.card_add_two_mul_card_eq_rank F
    omega
  have hpos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4
  refine (Nat.le_of_dvd hpos (Dvd.intro_left _ e.symm)).trans ?_
  calc _ = Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (H0 (twDual μ ρ)) * archH0Card S ρ c) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul b2 b4))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.LocHoms
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem rescale {l : ℕ} [Fact l.Prime] (a : ZMod (l ^ 1)) (ha : a ≠ 0) : ∃ b : ZMod (l ^ 1), b * a = 1 := by
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  exact ⟨a⁻¹, inv_mul_cancel₀ ha⟩

theorem UpperTheory.V.Ws.Gys.locHoms :
    LocalTateDuality → LocalEulerChar → UnramifiedOrthogonality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ g ∈ Dec (F := F) A, cycMod F Ω l 1 g = 1) →
      ∃ φ₁ ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))), ∃ φ₂ ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))),
        (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → φ₁ g = 0) ∧ (∃ g, φ₁ g = 1) ∧ ∃ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ∧ φ₂ g = 1 := by
  intro hT hE hU F Ω _ _ _ _ _ l _ A v hA hl hμ
  obtain ⟨f, hf, hf0⟩ := UpperTheory.V.Ws.Gys.locNe hT hE F Ω l A v hA hl hμ
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let ρ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1)) := Representation.trivial _ _ _
  let χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype
  have hχ : ∀ g, χ g = 1 := fun g => hμ g.1 g.2
  have hc : ContAction ρ := continuous_snd
  obtain ⟨hU1, hU2⟩ := hU F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hl (fun _ _ => rfl) hc
  have hinj := (hT F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hc).2.2.1.1
  let T : ZMod (l ^ 1) → TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) := fun t => TDual.mk (LinearMap.mul _ _ t)
  have htriv : ∀ g (m : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))), twDual χ ρ g m = m := fun g m => by
    apply DFunLike.ext
    intro t
    rw [twDual_apply, hχ, Units.val_one, one_mul]
    rfl
  let y : Z1 (twDual χ ρ) := ⟨fun g => T (f g), (continuous_of_discreteTopology (f := T)).comp hf.1, fun g h => by
    rw [htriv]
    apply DFunLike.ext
    intro m
    change f (g * h) * m = f g * m + f h * m
    rw [hf.2, add_mul]
    rfl⟩
  have hy : ∀ g (m : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))), y.1 g = twDual χ ρ g m - m → f g = 0 := fun g m h => by
    rw [htriv, sub_self] at h
    have h1 := congrArg (fun φ : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) => φ 1) h
    change f g * 1 = 0 at h1
    rwa [mul_one] at h1
  have ha : ∃ φ ∈ Z1 ρ, (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → φ g = 0) ∧ φ ≠ 0 := by
    by_contra H
    push Not at H
    refine hf0 (H f hf fun g hg => ?_)
    have h := (hU2 (Submodule.Quotient.mk y)).2 fun x hx => by
      induction x using Submodule.Quotient.induction_on with | H x =>
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
      have : x = 0 := Subtype.ext (H x.1 x.2 fun g hg => (hm ⟨g, hg⟩).trans (sub_self _))
      rw [this]
      exact map_zero _
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    exact hy g m (hm ⟨g, hg⟩)
  have hb : ∃ φ ∈ Z1 ρ, ∃ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ∧ φ g ≠ 0 := by
    by_contra H
    push Not at H
    have hyu : (Submodule.Quotient.mk y : H1 (twDual χ ρ)) ∈
        H1ur (twDual χ ρ) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun j => ?_⟩)
      rw [map_zero, sub_zero]
      apply DFunLike.ext
      intro m
      change f j.1 * m = 0
      rw [H f hf j.1 j.2, zero_mul]
    have h0 : (Submodule.Quotient.mk y : H1 (twDual χ ρ)) = 0 := by
      refine hinj ?_
      refine Eq.trans ?_ (map_zero _).symm
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with | H x =>
      exact (hU1 (Submodule.Quotient.mk x)).1
        ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2
          ⟨0, fun j => (H x.1 x.2 j.1 j.2).trans (sub_self _).symm⟩)) _ hyu
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
    exact hf0 (funext fun g => hy g m (hm g))
  obtain ⟨φ₁, h₁, hI, hne⟩ := ha
  obtain ⟨φ₂, h₂, g₂, hg₂, hne₂⟩ := hb
  obtain ⟨g₁, hg₁⟩ := Function.ne_iff.1 hne
  obtain ⟨b₁, e₁⟩ := rescale _ hg₁
  obtain ⟨b₂, e₂⟩ := rescale _ hne₂
  refine ⟨b₁ • φ₁, Submodule.smul_mem _ _ h₁, b₂ • φ₂, Submodule.smul_mem _ _ h₂, fun g hg => ?_, ⟨g₁, e₁⟩, g₂, hg₂, e₂⟩
  rw [Pi.smul_apply, hI g hg, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SelMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.selMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), S₀ ⊆ S →
      (∀ v ∈ S, v ∉ S₀ → TrivAt l (ρ.comp (toGS Ω _)) v) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ (m0 : M) (f : Z1 ρ),
        Submodule.Quotient.mk f ∈ gysSel S₀ S ρ Av m0 →
        (fun g => f.1 (toGS Ω _ g)) ∈ Zunr (ρ.comp (toGS Ω _)) S ∧
        (∀ v ∈ S₀, ∀ A, IsPlaceOver A v → ∃ m, ∀ g ∈ Dec (F := F) A, f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m) ∧
        ∀ v : S, v.1 ∉ S₀ → ∀ g ∈ Ine (F := F) (Av v), f.1 (toGS Ω _ g) ∈ Submodule.span R {m0} := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ _ _ S₀ S ρ hS htriv Av hA m0 f hf
  have hZ : (fun g => f.1 (toGS Ω _ g)) ∈ Z1 (ρ.comp (toGS Ω _) : Representation R (G F Ω) M) :=
    ⟨f.2.1.comp QuotientGroup.continuous_mk, fun a b => by
      have := f.2.2 (toGS Ω _ a) (toGS Ω _ b)
      rw [← map_mul] at this
      exact this⟩
  have hloc := (mem_Sel _ _ _ _ _).1 hf
  refine ⟨⟨hZ, fun v hv A hAv g hg => ?_⟩, fun v hv A hAv => ?_, fun v hv g hg => ?_⟩
  · have h1 : f.1 1 = 0 := by
      have := f.2.2 1 1
      rw [one_mul, map_one] at this
      exact left_eq_add.1 this
    have h2 : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g = 1 := by
      refine (QuotientGroup.eq_one_iff g).2 ?_
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hv, A, hAv, hg⟩
    show f.1 (toGS Ω _ g) = 0
    rw [h2, h1]
  · have h := hloc ⟨v, hS hv⟩
    rw [show gysL S₀ S ρ Av m0 ⟨v, hS hv⟩ = ⊥ from if_pos hv, Submodule.mem_bot] at h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    exact (UpperTheory.V.Ws.Gys.cocConj F Ω R M (ρ.comp (toGS Ω _)) _ hZ v (Av ⟨v, hS hv⟩) A (hA ⟨v, hS hv⟩) hAv).1
      ⟨m, fun g hg => hm ⟨g, hg⟩⟩
  · have h := hloc v
    rw [show gysL S₀ S ρ Av m0 v = ramLine (ρ.comp (locFam S Av v)) ((Ine (F := F) (Av v)).subgroupOf (Dec (F := F) (Av v))) m0
      from if_neg hv, mem_ramLine] at h
    obtain ⟨f', h1, h2⟩ := h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 h2)
    have hd : g ∈ Dec (F := F) (Av v) := Ine_le_Dec _ hg
    have h3 := hm ⟨g, hd⟩
    have h4 : ρ (toGS Ω _ g) = 1 := (htriv v.1 v.2 hv (Av v) (hA v) g hd).1
    have h5 : f'.1 ⟨g, hd⟩ - f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := h3
    rw [h4, Module.End.one_apply, sub_self, sub_eq_zero] at h5
    rw [← h5]
    exact h1 ⟨g, hd⟩ hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.ZunrFin
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M]

private theorem coc_one {ρ : Representation R Γ M} {c : Γ → M} (hc : c ∈ Z1 ρ) : c 1 = 0 := by
  have h := hc.2 1 1
  simpa using h

private def killSub (ρ : Representation R Γ M) {c : Γ → M} (hc : c ∈ Z1 ρ) : Subgroup Γ where
  carrier := {g | ρ g = 1 ∧ c g = 0}
  one_mem' := ⟨map_one ρ, coc_one hc⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [map_mul, ha, hb, one_mul], by rw [hc.2, ha', hb', map_zero, add_zero]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have : ρ (a * a⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
      rwa [map_mul, ha, one_mul] at this
    refine ⟨h1, ?_⟩
    have h := hc.2 a a⁻¹
    rw [mul_inv_cancel, coc_one hc, ha', ha] at h
    simpa using h.symm

private theorem killSub_normal (ρ : Representation R Γ M) {c : Γ → M} (hc : c ∈ Z1 ρ) : (killSub ρ hc).Normal where
  conj_mem := by
    rintro g ⟨hg, hg'⟩ h
    refine ⟨by rw [map_mul, map_mul, hg, mul_one, ← map_mul, mul_inv_cancel, map_one], ?_⟩
    have e := hc.2 h h⁻¹
    rw [mul_inv_cancel, coc_one hc] at e
    rw [hc.2, hc.2, hg', map_zero, add_zero, map_mul, hg, mul_one]
    exact e.symm

private theorem killSub_closed (ρ : Representation R Γ M) (hρ : ContAction ρ) {c : Γ → M} (hc : c ∈ Z1 ρ) :
    IsClosed (killSub ρ hc : Set Γ) := by
  have e : (killSub ρ hc : Set Γ) = (⋂ m : M, {g | ρ g m = m}) ∩ {g | c g = 0} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact and_congr_left' LinearMap.ext_iff
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun m => isClosed_eq ?_ continuous_const) (isClosed_eq hc.1 continuous_const)
  exact Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) hρ (continuous_id.prodMk continuous_const)

private theorem module_finite_z1_padicInt [Finite M] (ρ : Representation R Γ M) [Finite (H1 ρ)] : Finite (Z1 ρ) := by
  haveI : Finite (B1 ρ) := (Set.finite_range (d0 ρ)).to_subtype
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : B1 ρ => z.1) h))
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup := this
  haveI : Finite (Z1 ρ ⧸ ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup) := ‹Finite (H1 ρ)›
  exact Finite.of_addSubgroup_quotient ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup

end

theorem UpperTheory.V.Ws.Gys.zunrFin :
    GlobalFiniteness → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod (l ^ 1)) (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ContAction ρ → UnrOut ρ S → (Zunr ρ S).Finite := by
  intro hGF F Ω _ _ _ _ _ l _ M _ _ _ _ _ ρ S hS hρ hU
  obtain ⟨ρS, hcomp, hρS⟩ := UpperTheory.V.Ws.Gys.descend F Ω _ M ρ S hρ hU
  obtain ⟨-, f1, -⟩ := hGF F Ω l 1 M S ρS one_pos hS hρS
  haveI := f1
  haveI := module_finite_z1_padicInt ρS
  refine (Set.finite_range fun c : Z1 ρS => c.1 ∘ toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))).subset ?_
  rintro c ⟨hc, hI⟩
  haveI := killSub_normal ρ hc
  have hle : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ killSub ρ hc := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => ?_) (killSub_closed ρ hρ hc)
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    exact ⟨hU v hv A hA g hg, hI v hv A hA g hg⟩
  let cS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M := Quotient.lift c fun a b hab => by
    have h := (hle (QuotientGroup.leftRel_apply.1 hab)).2
    have e := hc.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h, map_zero, add_zero] at e
    exact e.symm
  refine ⟨⟨cS, hc.1.quotient_lift _, fun x y => ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have e := hc.2 a b
  rw [← hcomp] at e
  exact e
end

