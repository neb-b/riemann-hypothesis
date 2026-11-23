module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.IpEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.ipEq :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), (∀ u, (residOf r).Ip u = r.Ip u ∧ (residOf r).Ip u = (globOf r V0).frame.Iu u) ∧ ∀ [IsNoetherianRing O] (B : UniversalOrdinaryDeterminantRing r), augmentationIdealKernel (pairOf B.u) = {z | z ∈ B.GroupAlgebraKernelIdeal} := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ n r
  have h1 : ∀ u, (residOf r).Ip u = r.Ip u := by
    intro u
    refine le_antisymm (residOf_Ip_le r u) ?_
    rintro g ⟨⟨γ, hγ, rfl⟩, h2⟩
    refine ⟨⟨⟨γ, Ine_le_Dec _ hγ⟩, ⟨hγ, ?_⟩, rfl⟩, h2⟩
    exact Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h2 i
  have h2 : ∀ u, (residOf r).Ip u = (globOf r V0).frame.Iu u := by
    intro u
    refine le_antisymm inf_le_left (le_inf le_rfl ?_)
    rintro g ⟨γ, ⟨-, h⟩, rfl⟩
    exact Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h i
  refine ⟨fun u => ⟨h1 u, h2 u⟩, ?_⟩
  intro _ B
  have h3 : (pairOf B.u).D.CH ∪ pairGens (pairOf B.u) = B.E0gens := by
    unfold pairGens UniversalOrdinaryDeterminantRing.E0gens
    simp only [h1]
    rw [Set.union_assoc]
    rfl
  have h4 : (pairOf B.u).D.chBar (pairGens (pairOf B.u)) = B.GroupAlgebraKernelIdeal :=
    congrArg (closureIdeal (maximalIdeal B.B)) h3
  exact congrArg (fun K : TwoSidedIdeal (MonoidAlgebra B.B V0.frame.G₀) => {z | z ∈ K}) h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.LevUp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.levUp :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (Q : Set (Plc (Lp L))), Q.Finite → (∀ v ∈ Q, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Dec (F := Lp L) B ≤ (resP L Ω).range) → ∃ V : s.Lev, V.S' = V0.S' ∪ Q ∧ ∃ h : (globOf r V).Hom (globOf r V0), ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ n r Q hQ hQs
  have hsub : (⋃ v ∈ (V0.S' ∪ Q)ᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := Lp L) A) ⊆
      ⋃ v ∈ V0.S'ᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := Lp L) A :=
    Set.biUnion_subset_biUnion_left (Set.compl_subset_compl.mpr Set.subset_union_left)
  have hNS : NS Ω (V0.S' ∪ Q) ≤ NS Ω V0.S' :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.normalClosure_mono hsub).trans (Subgroup.le_topologicalClosure _))
      (Subgroup.isClosed_topologicalClosure _)
  let π : GS Ω (V0.S' ∪ Q) →* GS Ω V0.S' :=
    QuotientGroup.map _ _ (MonoidHom.id _) (fun x hx => hNS hx)
  have hπ : ∀ g, π (toGS Ω (V0.S' ∪ Q) g) = toGS Ω V0.S' g := fun g => rfl
  have hπc : Continuous π := by
    refine (QuotientGroup.isQuotientMap_mk (NS Ω (V0.S' ∪ Q))).continuous_iff.mpr ?_
    exact continuous_toGS Ω V0.S'
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V0.S') y
    exact ⟨toGS Ω (V0.S' ∪ Q) g, rfl⟩
  have hconj : ∀ σ h, h ∈ (resP L Ω).range → σ * h * σ⁻¹ ∈ (resP L Ω).range := by
    intro σ h hh
    rw [← V0.hη] at hh ⊢
    simp [hh]
  refine ⟨{ S' := V0.S' ∪ Q
            fin := V0.fin.union hQ
            sub := V0.sub.trans Set.subset_union_left
            split := ?_
            η := V0.η.comp π
            hη := fun g => by simpa only [MonoidHom.comp_apply, hπ] using V0.hη g
            η_open := V0.η_open.preimage hπc
            η_c := by simpa only [MonoidHom.comp_apply, hπ] using V0.η_c
            ε := V0.ε.comp π
            hε := by
              ext g : 1
              simpa only [MonoidHom.comp_apply, hπ] using DFunLike.congr_fun V0.hε g
            ε_cont := V0.ε_cont.comp hπc }, rfl, ?_⟩
  · intro v hv
    rcases hv with hv | hv
    · exact V0.split v hv
    · obtain ⟨B, hB, hdec⟩ := hQs v hv
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB (s.hA v)
      intro τ hτ
      have hτ' : σ⁻¹ * τ * σ ∈ Dec (F := Lp L) B := by
        open Pointwise in
        rw [mem_Dec, mul_smul, mul_smul, hσ, mem_Dec.mp hτ, ← hσ, inv_smul_smul]
      have := hconj σ _ (hdec hτ')
      simpa [mul_assoc] using this
  · exact ⟨⟨π, hπc, hπs, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun _ => rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiDec
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  simpa [mul_assoc] using QuotientGroup.eq.1 h

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  letI : TopologicalSpace (ZMod n) := ⊥
  haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩
  have hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x := fun x => continuous_inv.smul continuous_const
  have hc : ContAction (permR (ZMod n) H) := by
    refine continuous_pi fun x => ?_
    have h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2 := continuous_of_discreteTopology
    exact h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))
  haveI h1 := h _ _ hc
  haveI : Finite (Z1 (permR (ZMod n) H)) := by
    have hB : Finite (B1 (permR (ZMod n) H)) := (Set.finite_range _).to_subtype
    have hB' : Finite ((B1 (permR (ZMod n) H)).comap (Z1 (permR (ZMod n) H)).subtype).toAddSubgroup :=
      Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : B1 (permR (ZMod n) H)))
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    exact @Finite.of_addSubgroup_quotient _ _ _ hB' h1
  have hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ := fun φ hφ =>
    continuous_of_continuousAt_one φ (by
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]
      exact hφ.mem_nhds φ.ker.one_mem)
  let c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → Z1 (permR (ZMod n) H) := fun φ =>
    ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, sec_mem H g x⟩), by
      refine ⟨continuous_pi fun x => continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩
      · exact (continuous_const.mul continuous_id).mul
          ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))
      · funext x
        rw [Pi.add_apply, permR_apply, ← toAdd_mul, ← map_mul]
        refine congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)
        simp [mul_smul, mul_assoc]⟩
  refine Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)
  let x : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hx : x.out ∈ H := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm
    simpa using this
  have hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x := by
    change (((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)
  have hu : (⟨_, sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u := by
    apply Subtype.ext
    simp only [hfix]
    group
  have := congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x
  simp only [c, hu] at this
  exact Multiplicative.toAdd.injective this

theorem UpperTheory.V.Pa.phiDec :
    LocalFiniteness → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → PhiCond (Dec (F := F) A) l := by
  intro hLF l hl F Ω _ _ _ _ _ A v hA
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (Dec (F := F) A) (l ^ 1) := phi_condition_of_finite_cohomology (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
    obtain ⟨-, f1, -⟩ := hLF F Ω l 1 M A ρ v one_pos hA hρ
    exact f1
  rwa [pow_one] at key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.ProkerPL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prokerPL :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (I : Type) [Group I] [TopologicalSpace I] [IsTopologicalGroup I] (f : I →* Γ) (H : Subgroup Γ), Continuous f → (∀ g, f g ∈ H) → ∀ g ∈ GlobalTheory.TameQuot.proKer l I, f g ∈ PL l H := by
  intro l _ Γ _ _ _ _ _ I _ _ _ f H hf hfH g hg
  unfold PL
  simp only [Subgroup.mem_iInf]
  intro U hU
  let φ : I →* Γ ⧸ U.toSubgroup := (QuotientGroup.mk' U.toSubgroup).comp f
  haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  have hp : IsPGroup l φ.range := by
    rintro ⟨y, x, rfl⟩
    obtain ⟨e, he⟩ := hU (f x) (hfH x)
    refine ⟨e, Subtype.ext ?_⟩
    show φ x ^ l ^ e = 1
    rw [← map_pow]
    show (QuotientGroup.mk (f (x ^ l ^ e)) : Γ ⧸ U.toSubgroup) = 1
    rw [QuotientGroup.eq_one_iff, map_pow]
    exact he
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  have hker : φ.ker = U.toSubgroup.comap f := by
    ext x
    simp [φ, QuotientGroup.eq_one_iff]
  have hopen : IsOpen (φ.ker : Set I) := by
    rw [hker]
    exact U.isOpen.preimage hf
  have h2 := GlobalTheory.TameQuot.mem_proKer.1 hg φ.ker inferInstance hopen
    ⟨n, by rw [Subgroup.index_ker, hn]⟩
  rw [hker] at h2
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.StarSingle
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem star_single' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (b : R) :
    F.star O R n (MonoidAlgebra.single g b) =
      MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp]

private theorem star_sub' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (x y : MonoidAlgebra R F.G₀) :
    F.star O R n (x - y) = F.star O R n x - F.star O R n y := by
  simp [GFrame.star]

end UpperTheory.V.Pa

private theorem chib_conj_eq_one_of_chib_eq_one_of_eps_eq_one {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid F O n) (x : F.G₀) (hχ : ∀ i, r.chib i x = 1)
    (he : F.eps O (ResidueField O) x = 1) (j : Fin n) :
    r.chib j (F.conj x) = 1 := by
  have hD : ∀ (y : F.G₀) (t : ResidueField O),
      (GDet.ofRep (diagRep r.chib)).D (ResidueField O) (MonoidAlgebra.single y t - 1) =
        ∏ i, (((r.chib i y : (ResidueField O)ˣ) : ResidueField O) * t - 1) := by
    intro y t
    simp only [GDet.ofRep, GDet.repAlg, diagRep]
    simp
    have e : (t • Matrix.diagonal fun i ↦ ((r.chib i y : (ResidueField O)ˣ) : ResidueField O)) - 1 =
        Matrix.diagonal fun i ↦ ((r.chib i y : (ResidueField O)ˣ) : ResidueField O) * t - 1 := by
      ext i k
      by_cases h : i = k
      · subst h; simp [mul_comm]
      · simp [Matrix.diagonal, Matrix.one_apply, h]
    rw [e, Matrix.det_diagonal]
  set t : ResidueField O := ((r.chib j (F.conj x) : (ResidueField O)ˣ) : ResidueField O) with ht
  have hs : F.star O (ResidueField O) n (MonoidAlgebra.single x t - 1) =
      MonoidAlgebra.single (F.conj x)⁻¹ t - 1 := by
    rw [star_sub', star_single', he]
    congr 1
    · simp
    · rw [MonoidAlgebra.one_def, star_single']
      simp
  have hp := r.polar (ResidueField O) (MonoidAlgebra.single x t - 1)
  rw [hs, hD, hD] at hp
  simp only [hχ, Units.val_one, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  have h0 : ∏ i, (((r.chib i (F.conj x)⁻¹ : (ResidueField O)ˣ) : ResidueField O) * t - 1) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [ht, map_inv, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _), sub_self]
  rw [h0] at hp
  have h1 : t - 1 = 0 := (pow_eq_zero_iff (Fin.pos j).ne').mp hp.symm
  ext
  simpa [ht, sub_eq_zero] using h1

private theorem eps_residueField_eq_one_of_toZMod_eq_one {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] [CharP (ResidueField O) l] (x : F.G₀)
    (hx : PadicInt.toZMod ((F.ε x : ℤ_[l]ˣ) : ℤ_[l]) = 1) :
    F.eps O (ResidueField O) x = 1 := by
  have hm : ((F.ε x : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, hx, map_one, sub_self]
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  ext
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Units.coe_map, Units.val_one]
  have key := congrArg (algebraMap ℤ_[l] (ResidueField O)) hw
  simp only [map_sub, map_one, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_eq_zero] at key
  simpa [IsScalarTower.algebraMap_apply ℤ_[l] O (ResidueField O)] using key

theorem UpperTheory.V.Pa.hEx :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) [CharP (ResidueField O) l] (r : Resid F O n), ∃ H : OpenNormalSubgroup F.Γ, ∀ g : F.Γ, g ∈ H ↔ ∃ h : F.η g = 1, (∀ i, r.chib i ⟨g, h⟩ = 1) ∧ PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  intro l _ F O _ _ _ n _ r
  let P : F.Γ → Prop := fun g => ∃ h : F.η g = 1, (∀ i, r.chib i ⟨g, h⟩ = 1) ∧
    PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1
  let S : Subgroup F.Γ :=
    { carrier := {g | P g}
      mul_mem' := by
        rintro a b ⟨ha, hχa, hεa⟩ ⟨hb, hχb, hεb⟩
        refine ⟨by simp [ha, hb], fun i => ?_, ?_⟩
        · show r.chib i (⟨a, ha⟩ * ⟨b, hb⟩) = 1
          rw [map_mul, hχa, hχb, one_mul]
        · rw [map_mul, Units.val_mul, map_mul, hεa, hεb, one_mul]
      one_mem' := by
        refine ⟨by simp, fun i => ?_, ?_⟩
        · show r.chib i 1 = 1
          exact map_one _
        · simp
      inv_mem' := by
        rintro a ⟨ha, hχa, hεa⟩
        refine ⟨by simp [ha], fun i => ?_, ?_⟩
        · show r.chib i (⟨a, ha⟩)⁻¹ = 1
          rw [map_inv, hχa, inv_one]
        · have hu : ((F.ε a⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * ((F.ε a : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
            rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
          have := congrArg PadicInt.toZMod hu
          rw [map_mul, hεa, mul_one, map_one] at this
          exact this }
  have hmem : ∀ g, g ∈ S ↔ P g := fun g => Iff.rfl
  have hopen : IsOpen (S : Set F.Γ) := by
    have h1 : IsOpen {x : F.G₀ | ∀ i, r.chib i x = 1} := by
      have e : {x : F.G₀ | ∀ i, r.chib i x = 1} = ⋂ i, ((r.chib i).ker : Set F.G₀) := by
        ext x
        simp [MonoidHom.mem_ker]
      rw [e]
      exact isOpen_iInter_of_finite fun i => r.chib_open i
    have h2 : IsOpen {x : F.G₀ | PadicInt.toZMod ((F.ε x : ℤ_[l]ˣ) : ℤ_[l]) = 1} := by
      have e : ∀ z : ℤ_[l], PadicInt.toZMod z = 1 ↔ ‖z - 1‖ < 1 := by
        intro z
        rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod,
          RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      simp_rw [e]
      exact isOpen_lt (continuous_norm.comp ((Units.continuous_val.comp
        (F.ε_cont.comp continuous_subtype_val)).sub continuous_const)) continuous_const
    have e : (S : Set F.Γ) = Subtype.val ''
        ({x : F.G₀ | ∀ i, r.chib i x = 1} ∩ {x : F.G₀ | PadicInt.toZMod ((F.ε x : ℤ_[l]ˣ) : ℤ_[l]) = 1}) := by
      ext g
      constructor
      · rintro ⟨h, hχ, hε⟩
        exact ⟨⟨g, h⟩, ⟨hχ, hε⟩, rfl⟩
      · rintro ⟨x, ⟨hχ, hε⟩, rfl⟩
        exact ⟨x.2, hχ, hε⟩
    rw [e]
    exact F.η_open.isOpenMap_subtype_val _ (h1.inter h2)
  have case1 : ∀ g, P g → ∀ a, F.η a = 1 → P (a * g * a⁻¹) := by
    rintro g ⟨h, hχ, hε⟩ a ha
    refine ⟨by simp [h, ha], fun i => ?_, ?_⟩
    · show r.chib i (⟨a, ha⟩ * ⟨g, h⟩ * (⟨a, ha⟩)⁻¹) = 1
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
      exact hχ i
    · rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
      exact hε
  have hnorm : S.Normal := by
    refine ⟨fun g hg a => ?_⟩
    rw [hmem] at hg ⊢
    rcases Int.units_eq_one_or (F.η a) with ha | ha
    · exact case1 g hg a ha
    · have hb : F.η (F.c⁻¹ * a) = 1 := by
        rw [map_mul, map_inv, F.η_c, ha]
        rfl
      obtain ⟨h', hχ', hε'⟩ := case1 g hg (F.c⁻¹ * a) hb
      obtain ⟨h, -, hε⟩ := hg
      have hη : F.η (a * g * a⁻¹) = 1 := by simp [h]
      have hx : (⟨a * g * a⁻¹, hη⟩ : F.G₀) = F.conj ⟨F.c⁻¹ * a * g * (F.c⁻¹ * a)⁻¹, h'⟩ := by
        apply Subtype.ext
        simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk]
        group
      refine ⟨hη, fun i => ?_, ?_⟩
      · rw [hx]
        exact chib_conj_eq_one_of_chib_eq_one_of_eps_eq_one F O n r _ hχ' (eps_residueField_eq_one_of_toZMod_eq_one F O _ hε') i
      · rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
        exact hε
  exact ⟨⟨⟨S, hopen⟩, hnorm⟩, fun g => Iff.rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.UnipPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charK (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI := hp
  have hpp : p.Prime := CharP.char_is_prime K p
  by_contra hne
  have hpl : p ≠ l := fun h => hne (h ▸ hp)
  have hu : IsUnit (p : ℤ_[l]) := by
    by_contra h
    rw [PadicInt.not_isUnit_iff, ← Int.cast_natCast, PadicInt.norm_int_lt_one_iff_dvd,
      Int.natCast_dvd_natCast] at h
    exact hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out) hpp).mp h).symm
  have := hu.map (algebraMap ℤ_[l] K)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

private theorem unip_pow (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [CharP K l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hM : (M.map (PowerSeries.constantCoeff : PowerSeries K →+* K)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n * m) - 1) i j ∈ maximalIdeal (PowerSeries K) ^ m := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact (IsEmpty.false i).elim
  haveI : CharP (PowerSeries K) l :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective l
  set N := M - 1 with hN
  have hMN : M = 1 + N := by rw [hN]; abel
  have hfrob : M ^ l ^ (n * m) - 1 = N ^ l ^ (n * m) := by
    rw [hMN, add_pow_char_pow_of_commute (p := l) (h := Commute.one_left N), one_pow, add_sub_cancel_left]
  let f := (PowerSeries.constantCoeff : PowerSeries K →+* K).mapMatrix (m := Fin n)
  have hNn : f (N ^ n) = 0 := by
    rw [map_pow, hN, map_sub, map_one, RingHom.mapMatrix_apply]
    have := Matrix.aeval_self_charpoly (M.map PowerSeries.constantCoeff)
    rw [hM] at this
    simpa [map_pow, map_sub] using this
  have h1 : ∀ a b, (N ^ n) a b ∈ maximalIdeal (PowerSeries K) := by
    intro a b
    have h0 : PowerSeries.constantCoeff ((N ^ n) a b) = 0 := by
      have := congrFun (congrFun hNn a) b
      simpa [f, RingHom.mapMatrix_apply] using this
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, h0]
    exact not_isUnit_zero
  have hpow : ∀ (I : Ideal (PowerSeries K)) (P : Matrix (Fin n) (Fin n) (PowerSeries K)),
      (∀ a b, P a b ∈ I) → ∀ k : ℕ, ∀ a b, (P ^ k) a b ∈ I ^ k := by
    intro I P hP k
    induction k with
    | zero => intro a b; simp [Ideal.one_eq_top]
    | succ k ih =>
      intro a b
      rw [pow_succ P, Matrix.mul_apply, pow_succ I]
      exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (ih a c) (hP c b)
  have hle : n * m ≤ l ^ (n * m) := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  rw [hfrob, show l ^ (n * m) = n * m + (l ^ (n * m) - n * m) by omega, pow_add, pow_mul,
    Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hpow _ _ h1 m i c)

theorem UpperTheory.V.Pa.rhoPL :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (H : OpenNormalSubgroup F.Γ), (∀ g ∈ H, ∃ h : F.η g = 1, ((mat x.ρ ⟨g, h⟩).map (PowerSeries.constantCoeff : x.A →+* x.K)).charpoly = (Polynomial.X - 1) ^ n) → ∀ g : F.G₀, (g : F.Γ) ∈ PL l H.toSubgroup → x.ρ g = 1 := by
  intro l _ F n x H hH g hg
  haveI : CharP x.K l := charK l x.K
  have key : ∀ m : ℕ, ∀ i j, (mat x.ρ g - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m := by
    intro m
    let φ : F.G₀ →* Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m) :=
      (Ideal.Quotient.mk (maximalIdeal (PowerSeries x.K) ^ m)).mapMatrix.toMonoidHom.comp (mat x.ρ)
    have hφ : ∀ y, φ y = 1 ↔ ∀ i j, (mat x.ρ y - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m := by
      intro y
      rw [← Matrix.ext_iff]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
      show Ideal.Quotient.mk _ (mat x.ρ y i j) =
          (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j ↔ _
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    let T : Subgroup F.Γ := φ.ker.map F.η.ker.subtype
    have hTopen : IsOpen (T : Set F.Γ) := by
      have hK : IsOpen (φ.ker : Set F.G₀) := by
        have e : (φ.ker : Set F.G₀) = ⋂ i, ⋂ j, {y : F.G₀ | φ y i j =
            (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j} := by
          ext y
          simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
          exact Matrix.ext_iff.symm
        rw [e]
        exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
          (x.cont i j m : IsLocallyConstant fun y : F.G₀ => φ y i j).isOpen_fiber _
      rw [Subgroup.coe_map]
      exact F.η_open.isOpenMap_subtype_val _ hK
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hTopen T.one_mem
    let W : OpenNormalSubgroup F.Γ :=
      { toSubgroup := T.normalCore
        isOpen' := Subgroup.isOpen_mono (H₁ := V.toSubgroup)
          (Subgroup.normal_le_normalCore.mpr fun a ha => hV ha) V.toOpenSubgroup.isOpen
        isNormal' := Subgroup.normalCore_normal T }
    have hW : ∀ h ∈ H.toSubgroup, ∃ e, h ^ l ^ e ∈ W := by
      intro h hh
      refine ⟨n * m, ?_⟩
      show ∀ b : F.Γ, b * h ^ l ^ (n * m) * b⁻¹ ∈ T
      intro b
      rw [← conj_pow]
      have hbh : b * h * b⁻¹ ∈ H.toSubgroup := H.isNormal'.conj_mem h hh b
      obtain ⟨he, hchar⟩ := hH _ hbh
      refine Subgroup.mem_map.mpr ⟨⟨b * h * b⁻¹, he⟩ ^ l ^ (n * m), ?_, by simp⟩
      rw [MonoidHom.mem_ker, hφ, map_pow]
      exact unip_pow l x.K n m _ hchar
    have hgW : (g : F.Γ) ∈ T.normalCore := by
      have h2 := hg
      simp only [UpperTheory.V.Pa.PL, Subgroup.mem_iInf] at h2
      exact h2 W hW
    have h1 := T.normalCore_le hgW
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp h1
    have hyg' : y = g := Subtype.ext hyg
    rw [← hyg']
    exact (hφ y).mp hy
  apply Units.ext
  show mat x.ρ g = 1
  refine Matrix.ext fun i j => ?_
  have h0 : (mat x.ρ g - 1) i j ∈ ⨅ m, maximalIdeal (PowerSeries x.K) ^ m :=
    Submodule.mem_iInf _ |>.mpr fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
    Ideal.mem_bot, Matrix.sub_apply, sub_eq_zero] at h0
  exact h0
end

