module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.PtTail
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GenDec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GwTame
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem ch_ur {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R D M) (J : Subgroup D) (hJ : ∀ j ∈ J, ∀ m, ρ j m = m)
    (z : Z1 ρ) : (Submodule.Quotient.mk z : H1 ρ) ∈ H1ur ρ J ↔ ∀ j ∈ J, z.1 j = 0 := by
  refine (Submodule.Quotient.mk_eq_zero _).trans ((mem_coboundaries1 _ _).trans ⟨fun ⟨m, hm⟩ j hj => ?_, fun h => ⟨0, fun j => ?_⟩⟩)
  · exact (hm ⟨j, hj⟩).trans (sub_eq_zero.2 (hJ j hj m))
  · rw [map_zero, sub_zero]
    exact h j.1 j.2

private theorem ch_low (hF : LocalFiniteness) (hT : LocalTateDuality) (hE : LocalEulerChar) {F Ω : Type} [Field F] [NumberField F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω)
    (hA : IsPlaceOver A v) (hv : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (K : Subgroup (G F Ω)) [K.Normal] (ho : IsOpen (K : Set (G F Ω)))
    (hi : ¬ l ∣ K.index) (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (G F Ω) M) (hρ : ContAction ρ) (hK : ∀ g ∈ K, ρ g = 1) :
    Nat.card (H0 (ρ.comp (Dec (F := F) A).subtype)) ≤
      Nat.card (H1ur (ρ.comp (Dec (F := F) A).subtype) ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A))) := by
  haveI : Module.Finite k M := Module.Finite.of_finite
  let σ : Representation k (Dec (F := F) A) M := ρ.comp (Dec (F := F) A).subtype
  obtain ⟨f1, -, -, e1, -⟩ := locEuler hF hT hE F Ω l v A hA k M σ
    (Continuous.comp hρ ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  obtain ⟨f2, e2⟩ := tameEq hF hT hE F Ω l v A hA hv K ho hi k M ρ hρ fun g hg => hK g hg.2
  let i : (Ine (F := F) A ⊓ K : Subgroup (G F Ω)) → Dec (F := F) A := fun j => ⟨j.1, Ine_le_Dec A j.2.1⟩
  have hi' : ∀ j m, σ (i j) m = m := fun j m => LinearMap.congr_fun (hK _ j.2.2) m
  let r : Z1 σ →ₗ[k] eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K) :=
    { toFun := fun z => ⟨fun j => z.1 (i j),
        (IsLocallyConstant.iff_continuous _).2 (z.2.1.comp (continuous_subtype_val.subtype_mk _)),
        fun a b => (z.2.2 (i a) (i b)).trans (by rw [hi']), fun d hd j j' h => by
          have e : i j' * ⟨d, hd⟩ = ⟨d, hd⟩ * i j := Subtype.ext (by
            show j'.1 * d = d * j.1
            rw [h, inv_mul_cancel_right])
          have e' := congrArg z.1 e
          rw [z.2.2, z.2.2, hi', add_comm] at e'
          exact add_left_cancel e'⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let r' : H1 σ →ₗ[k] eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K) := Submodule.liftQ _ r fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
    exact Subtype.ext (funext fun j => (hm (i j)).trans (sub_eq_zero.2 (hi' j m)))
  have hker : LinearMap.ker r' ≤ H1ur σ ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)) := by
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (ch_ur σ _ (fun j hj m => hi' ⟨j.1, hj⟩ m) z).2 fun j hj => ?_
    exact congrFun (congrArg Subtype.val (show r z = 0 from hx)) ⟨j.1, hj⟩
  have h1 := r'.finrank_range_add_finrank_ker
  have h2 := Submodule.finrank_mono hker
  have h3 := (LinearMap.range r').finrank_le
  have h4 := e1 hv
  change Nat.card (H0 σ) ≤ Nat.card (H1ur σ ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)))
  rw [Module.natCard_eq_pow_finrank (K := k) (V := H0 σ),
    Module.natCard_eq_pow_finrank (K := k) (V := H1ur σ ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)))]
  refine Nat.pow_le_pow_right Nat.card_pos ?_
  change _ = finrank k (H2 σ) at e2
  omega

private theorem ch_cup {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (hA : IsPlaceOver A v) (K : Subgroup (G F Ω)) [K.Normal]
    (ho : IsOpen (K : Set (G F Ω))) (hi : ¬ l ∣ K.index) (k : Type) [Field k] [Finite k] [CharP k l] [TopologicalSpace k]
    [DiscreteTopology k] (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
    {Γ : Type} [Group Γ] (μ : Γ →* kˣ) (ρ : Representation k Γ M) (φ : Dec (F := F) A →* Γ)
    (hρ : ContAction (ρ.comp φ)) (hμ : ContAction ((charRep μ).comp φ))
    (hK : ∀ g : Dec (F := F) A, g.1 ∈ K → ρ (φ g) = 1 ∧ μ (φ g) = 1)
    (y : Z1 ((twDual μ ρ).comp φ)) (hy : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ⊓ K → y.1 g = 0)
    (x : H1 (ρ.comp φ)) (hx : x ∈ H1ur (ρ.comp φ) ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A))) :
    cupH1H1TwistedDual μ ρ φ hρ (Submodule.Quotient.mk y) x = 0 := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  replace hx := (ch_ur _ ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A))
    (fun j hj m => LinearMap.congr_fun (hK j hj.2).1 m) x).1 hx
  obtain ⟨γ, -, h1, h2⟩ := decZhat F Ω v A hA
  haveI : ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)).Normal :=
    ⟨fun n hn g => ⟨conj_mem_Ine g.2 hn.1, Subgroup.Normal.conj_mem _ hn.2 _⟩⟩
  obtain ⟨b, hb1, -, hb2⟩ := H2_unramified_inflation l (Dec (F := F) A) k k ((charRep μ).comp φ) hμ
    ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)) γ
    (fun g hg => hg.1) (((isClosed_Ine A).inter (K.isClosed_of_isOpen ho)).preimage continuous_subtype_val)
    (by
      rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec A), Subgroup.inf_relIndex_left]
      exact fun h => hi (h.trans (Subgroup.relIndex_dvd_index_of_normal _ _)))
    (fun j hj => LinearMap.ext fun m => by simp [(hK j hj.2).2]) h1 h2
    (cupCocycleZ1Z1 ((twDual μ ρ).comp φ) (ρ.comp φ) ((charRep μ).comp φ) evalPair.flip
      continuous_of_discreteTopology (fun g y x => evalPair_equiv μ ρ (φ g) x y) hρ y x)
    (fun s t j hj j' hj' => by
      show y.1 (s * j) (ρ (φ (s * j)) (x.1 (t * j'))) = y.1 s (ρ (φ s) (x.1 t))
      rw [y.2.2, x.2.2, hy j hj, hx j' hj', map_zero, map_zero, add_zero, add_zero, map_mul, map_mul,
        (hK j hj.2).1, mul_one])
  exact (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2
    ⟨b, (IsLocallyConstant.iff_continuous _).1 hb1, funext fun p => (hb2 p.1 p.2).symm⟩)


open scoped Classical in
theorem UpperTheory.V.GC.gwTame (P : Hypotheses₂) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [Fact l.Prime] (hl : l ≠ 2) (S S' : Finset (HeightOneSpectrum (𝓞 F))) (hS : ContainsAbove S l) (hS' : ContainsAbove S' l)
    (A : S' → ValuationSubring Ω) (hA : ∀ v, IsPlaceOver (A v) v.1) (K : Subgroup (G F Ω)) [K.Normal]
    (ho : IsOpen (K : Set (G F Ω))) (hi : ¬ l ∣ K.index) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ)
    (μ : GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ 1))ˣ) (hμ : μ.comp (toGS Ω _) = cycMod F Ω l 1)
    (hK : ∀ g ∈ K, ρ (toGS Ω _ g) = 1 ∧ μ (toGS Ω _ g) = 1) (c : InfinitePlace F → G F Ω) (hc : ∀ w, IsCCAt w (c w))
    (X : Type) (f : X → Z1 (twDual μ ρ))
    (hf : Function.Injective fun x => (Submodule.Quotient.mk (f x) : H1 (twDual μ ρ)))
    (hf' : ∀ x (q : S'), q.1 ∉ S → ∀ g ∈ Ine (F := F) (A q) ⊓ K, (f x).1 (toGS Ω _ g) = 0) :
    Finite X ∧ Nat.card X ≤
      Nat.card {y : H1 ρ // ∃ z : Z1 ρ, Submodule.Quotient.mk z = y ∧
        ∀ v : S', ∀ g ∈ Ine (F := F) (A v) ⊓ K, z.1 (toGS Ω _ g) = 0} * Nat.card (H0 (twDual μ ρ)) *
      (∏ v : S', if v.1 ∈ S then Nat.card (H0 (ρ.comp (locFam S' A v))) else 1) * archH0Card S' ρ c := by
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  haveI : CharP (ZMod (l ^ 1)) l := CharP.congr (l ^ 1) (pow_one l)
  let L : LocCond ρ (locFam S' A) := fun v => if v.1 ∈ S then ⊥ else
    H1ur (ρ.comp (locFam S' A v)) ((Ine (F := F) (A v) ⊓ K).subgroupOf (Dec (F := F) (A v)))
  have hc' : ∀ v, ContAction (ρ.comp (locFam S' A v)) := fun v => hρ.comp' (continuous_locFam S' A v)
  have gw := P.gw F Ω l 1 M S' ρ one_pos hl hS' hρ μ hμ A hA c (fun w _ => hc w) L
  obtain ⟨-, f1, -⟩ := P.gf F Ω l 1 M S' ρ one_pos hS' hρ
  have f2 : ∀ v, Finite (H1 (ρ.comp (locFam S' A v))) := fun v => (P.lf F Ω l 1 M (A v) _ v.1 one_pos (hA v) (hc' v)).2.1
  haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
  have ha : 0 < archH0Card S' ρ c := by
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (Nat.pow_pos Nat.card_pos)
    haveI : Nonempty {m : M // ρ (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  have hmem : ∀ x, (Submodule.Quotient.mk (f x) : H1 (twDual μ ρ)) ∈ Sel (twDual μ ρ) (locFam S' A) (continuous_locFam S' A)
      (perpCond μ ρ (locFam S' A) hc' L) := by
    intro x
    rw [mem_Sel]
    intro v
    rw [mem_perpCond]
    intro y hy
    by_cases hv : v.1 ∈ S
    · simp only [L, if_pos hv, Submodule.mem_bot] at hy
      rw [hy, map_zero]
    · simp only [L, if_neg hv] at hy
      exact ch_cup l v.1 (A v) (hA v) K ho hi (ZMod (l ^ 1)) M μ ρ (locFam S' A v) (hc' v)
        ((GlobalTheory.Published.PoitouTate.contAction_charRep hμ).comp' (continuous_locFam S' A v)) (fun g hg => hK g.1 hg)
        (restrictCocycles1 _ _ (continuous_locFam S' A v) (f x)) (fun g hg => hf' x v hv g.1 hg) y hy
  have hpos : 0 < Nat.card (Sel ρ (locFam S' A) (continuous_locFam S' A) L) * Nat.card (H0 (twDual μ ρ)) *
      (∏ v : S', Nat.card (H0 (ρ.comp (locFam S' A v)))) * archH0Card S' ρ c :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) (Finset.prod_pos fun v _ => Nat.card_pos)) ha
  haveI : Finite (Sel (twDual μ ρ) (locFam S' A) (continuous_locFam S' A) (perpCond μ ρ (locFam S' A) hc' L)) := by
    refine Nat.finite_of_card_ne_zero fun h => ?_
    rw [gw, h, zero_mul, zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hinj : Function.Injective fun x => (⟨_, hmem x⟩ : Sel (twDual μ ρ) (locFam S' A) (continuous_locFam S' A)
      (perpCond μ ρ (locFam S' A) hc' L)) := fun a b h => hf (congrArg Subtype.val h)
  refine ⟨Finite.of_injective _ hinj, (Nat.card_le_card_of_injective _ hinj).trans ?_⟩
  have h1 : (∏ v : S', Nat.card (H0 (ρ.comp (locFam S' A v)))) ≤
      (∏ v : S', if v.1 ∈ S then Nat.card (H0 (ρ.comp (locFam S' A v))) else 1) * ∏ v : S', Nat.card (L v) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun v _ => ?_
    by_cases hv : v.1 ∈ S
    · rw [if_pos hv]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    · simp only [L, if_neg hv, one_mul]
      exact ch_low P.lf P.lt P.le l v.1 (A v) (hA v) (fun h => hv (hS _ h)) K ho hi (ZMod (l ^ 1)) M (ρ.comp (toGS Ω _))
        (hρ.comp' (continuous_toGS Ω _)) fun g hg => (hK g hg).1
  have h2 : Nat.card (Sel ρ (locFam S' A) (continuous_locFam S' A) L) ≤
      Nat.card {y : H1 ρ // ∃ z : Z1 ρ, Submodule.Quotient.mk z = y ∧
        ∀ v : S', ∀ g ∈ Ine (F := F) (A v) ⊓ K, z.1 (toGS Ω _ g) = 0} := by
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) fun a b h => Subtype.ext (Subtype.mk.inj h)
    obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨z, rfl, fun v g hg => ?_⟩
    have h3 : resH1 ρ _ (continuous_locFam S' A v) (Submodule.Quotient.mk z) ∈
        H1ur (ρ.comp (locFam S' A v)) ((Ine (F := F) (A v) ⊓ K).subgroupOf (Dec (F := F) (A v))) := by
      have := (mem_Sel _ _ _ _ _).1 hy v
      by_cases hv : v.1 ∈ S
      · simp only [L, if_pos hv, Submodule.mem_bot] at this
        rw [this]
        exact zero_mem _
      · simpa only [L, if_neg hv] using this
    exact (ch_ur _ ((Ine (F := F) (A v) ⊓ K).subgroupOf (Dec (F := F) (A v)))
      (fun j hj m => LinearMap.congr_fun (hK j.1 hj.2).1 m) (restrictCocycles1 ρ _ (continuous_locFam S' A v) z)).1 h3
      ⟨g, Ine_le_Dec _ hg.1⟩ hg
  have h3 : 0 < ∏ v : S', Nat.card (L v) := Finset.prod_pos fun v _ => Nat.card_pos
  have h4 : 0 < Nat.card (H0 ρ) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ h3
  refine (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h4)).trans (gw.ge.trans ?_)
  calc _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ h2) h1)
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.H2GaloisQuotientEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

section SlopeTestRemainingChoices

private theorem hg_rank {k V W : Type} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) [Module.Finite k (LinearMap.ker f)] [Module.Finite k W] (U : Submodule k V) (U' : Submodule k W)
    (h : ∀ x ∈ U, f x ∈ U') :
    Module.Finite k V ∧ finrank k U ≤ finrank k (LinearMap.ker f) + finrank k U' := by
  haveI : Module.Finite k V := by
    haveI := Module.Finite.equiv f.quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker f)
  refine ⟨this, ?_⟩
  have e := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  have a : finrank k (LinearMap.range (f.domRestrict U)) ≤ finrank k U' := Submodule.finrank_mono (by
    rintro _ ⟨x, rfl⟩
    exact h x.1 x.2)
  have b : finrank k (LinearMap.ker (f.domRestrict U)) ≤ finrank k (LinearMap.ker f) := by
    rw [← Submodule.finrank_map_subtype_eq]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  omega

private theorem hg_eqHom {k Γ Γ' M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
    [AddCommGroup M] [Module k M] (ρ : Representation k Γ' M) (t : Γ →* Γ') (ht : Continuous t) (D J : Subgroup Γ)
    [Module.Finite k (eqHom (ρ.comp t) D J)] :
    Module.Finite k (eqHom ρ (D.map t) (J.map t)) ∧
      finrank k (eqHom ρ (D.map t) (J.map t)) ≤ finrank k (eqHom (ρ.comp t) D J) := by
  let u : J → J.map t := fun j => ⟨t j.1, j.1, j.2, rfl⟩
  have hu : Continuous u := (ht.comp continuous_subtype_val).subtype_mk _
  let φ : eqHom ρ (D.map t) (J.map t) →ₗ[k] eqHom (ρ.comp t) D J :=
    { toFun := fun f => ⟨fun j => f.1 (u j), f.2.1.comp_continuous hu, fun a b => by
          rw [← f.2.2.1]
          exact congrArg f.1 (Subtype.ext (map_mul t a.1 b.1)),
        fun d hd j j' h => f.2.2.2 (t d) ⟨d, hd, rfl⟩ (u j) (u j') (by
          change t j'.1 = t d * t j.1 * (t d)⁻¹
          rw [h, map_mul, map_mul, map_inv])⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro f g h
    refine Subtype.ext (funext ?_)
    rintro ⟨_, j, hj, rfl⟩
    exact congrFun (congrArg Subtype.val h) ⟨j, hj⟩
  exact ⟨Module.Finite.of_injective φ hφ, LinearMap.finrank_le_finrank_of_injective hφ⟩

private theorem hg_loc {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [Fact l.Prime] {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    (K : Subgroup (G F Ω)) [K.Normal] (hK : IsOpen (K : Set (G F Ω))) (hl : ¬ l ∣ K.index)
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] (π : Dec (F := F) A →* Γ) (hπ : Continuous π)
    (h1 : ∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ⊓ K → π g = 1)
    {k : Type} [Field k] [Finite k] [CharP k l] {M : Type} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M) (hρ : ContAction ρ) (x : H2 ρ) :
    resH2 ρ π hπ x = 0 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  obtain ⟨φ, -, h2, h3⟩ := decZhat F Ω v A hA
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  haveI : ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)).Normal :=
    inferInstanceAs ((Ine (F := F) A).subgroupOf (Dec (F := F) A) ⊓ K.subgroupOf _).Normal
  obtain ⟨b, hb, -, hz⟩ := H2_unramified_inflation l (Dec (F := F) A) k M (ρ.comp π) (hρ.comp (hπ.prodMap continuous_id))
    ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ((Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)) φ
    (Subgroup.comap_mono inf_le_left)
    (((isClosed_Ine A).inter (K.isClosed_of_isOpen hK)).preimage continuous_subtype_val)
    (by
      rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]
      exact fun h => hl (h.trans (Subgroup.relIndex_dvd_index_of_normal _ _)))
    (fun j hj => by rw [MonoidHom.comp_apply, h1 j hj, map_one]) h2 h3 (restrictCocycles2 ρ π hπ z)
    (fun s t j hj j' hj' => by simp only [restrictCocycles2_apply, map_mul, h1 j hj, h1 j' hj', mul_one])
  change Submodule.Quotient.mk (restrictCocycles2 ρ π hπ z) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact (separated_dvr_second_cohomology_mem _ _).2 ⟨b, hb.continuous, funext fun p => (hz p.1 p.2).symm⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.GC.H2_galois_quotient_eq :
    Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], IsTotallyReal F → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ) (h : GLink l S K π) (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M), ContAction ρ →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, IsCCAt w (c w)) → ∀ (A : S → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) v.1) → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
    finrank k (Sha2 ρ (fun v => π.comp (Dec (F := F) (A v)).subtype) fun v => h.cont.comp continuous_subtype_val) + ∑ v, finrank k (H2 (ρ.comp (π.comp (Dec (F := F) (A v)).subtype))) + finrank k (H0 ρ) + finrank ℚ F * finrank k M ≤
      finrank k (H1 ρ) + ∑ w, finrank k (LinearMap.ker (ρ (π (c w)) - 1)) + finrank k (Loc.H0dual (cycF F Ω l k) (ρ.comp π)) := by
  intro P F Ω _ _ _ _ _ l _ hF S K Γ _ _ _ _ _ _ π h k _ _ _ M _ _ _ _ _ ρ hρ c hc A hA
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  haveI := h.normal
  obtain ⟨A', hA', rfl⟩ : ∃ A' : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (A' v) v) ∧
      A = fun v : S => A' v.1 := by
    refine ⟨fun v => if hv : v ∈ S then A ⟨v, hv⟩ else (exists_isPlaceOver Ω v).choose, fun v => ?_, funext fun v => ?_⟩
    · by_cases hv : v ∈ S
      · simpa only [dif_pos hv] using hA ⟨v, hv⟩
      · simpa only [dif_neg hv] using (exists_isPlaceOver Ω v).choose_spec
    · simp only [dif_pos v.2]
  obtain ⟨S', p, hSS, hp, hps, rfl, hker⟩ := levelS F Ω l S K Γ π h
  haveI hcl := isClosed_NS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))
  haveI : TotallyDisconnectedSpace (GS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))) :=
    (AlgebraTools.totallyDisconnected_quot _ _ hcl).1
  have hS' : ContainsAbove S' l := fun v hv => hSS (h.above v hv)
  have hρ' : ContAction (ρ.comp p) := hρ.comp (hp.prodMap continuous_id)
  have hkill : ∀ q, q ∉ S → ∀ g ∈ Ine (F := F) (A' q) ⊓ K, p (toGS Ω _ g) = 1 := by
    intro q hq g hg
    have : g ∈ (p.comp (toGS Ω _)).ker := by
      rw [h.ker]
      refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
      simp only [Set.mem_iUnion]
      exact ⟨q, hq, A' q, hA' q, hg⟩
    exact this
  let n : HeightOneSpectrum (𝓞 F) → ℕ := fun v =>
    finrank k (H2 ((ρ.comp p).comp (locHom (S' : Set (HeightOneSpectrum (𝓞 F))) (A' v))))
  have hq : ∀ q : {v // v ∈ S' ∧ v ∉ S},
      Module.Finite k (eqHom (ρ.comp p) ((Dec (F := F) (A' q.1)).map (toGS Ω _)) ((Ine (F := F) (A' q.1) ⊓ K).map (toGS Ω _))) ∧
      finrank k (eqHom (ρ.comp p) ((Dec (F := F) (A' q.1)).map (toGS Ω _)) ((Ine (F := F) (A' q.1) ⊓ K).map (toGS Ω _))) ≤
        n q.1 := by
    intro q
    obtain ⟨a1, a2⟩ := tameEq P.lf P.lt P.le F Ω l q.1 (A' q.1) (hA' _) (fun hv => q.2.2 (h.above _ hv)) K h.isOpen h.idx
      k M ((ρ.comp p).comp (toGS Ω _)) (hρ'.comp ((continuous_toGS Ω _).prodMap continuous_id))
      (fun g hg => by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hkill _ q.2.2 g hg, map_one])
    obtain ⟨b1, b2⟩ := hg_eqHom (ρ.comp p) (toGS Ω _) (continuous_toGS Ω _) (Dec (F := F) (A' q.1))
      (Ine (F := F) (A' q.1) ⊓ K)
    exact ⟨b1, b2.trans a2.le⟩
  obtain ⟨g1, g2, g3⟩ := globEuler P.gf P.ge F Ω l h.odd hF S' hS' k M (ρ.comp p) hρ' c hc
  have tail := ptTail P.lf P.gf P.pt F Ω l h.odd S' hS' (fun v => A' v.1) (fun v => hA' v.1) k M (ρ.comp p) hρ'
  letI : Fintype {v // v ∈ S' ∧ v ∉ S} := Fintype.subtype (S' \ S) fun _ => Finset.mem_sdiff
  obtain ⟨i1, i2, i3⟩ := inflKer l _ Γ p hp hps k M ρ hρ {v // v ∈ S' ∧ v ∉ S}
    (fun q => (Dec (F := F) (A' q.1)).map (toGS Ω _)) (fun q => (Ine (F := F) (A' q.1) ⊓ K).map (toGS Ω _))
    (hker A' hA') (fun q => (hq q).1) g1
  obtain ⟨r1, r2⟩ := hg_rank (resH2 ρ p hp)
    (Sha2 ρ (fun v : S => (p.comp (toGS Ω _)).comp (Dec (F := F) (A' v.1)).subtype) fun v => h.cont.comp continuous_subtype_val)
    (Sha2 (ρ.comp p) (fun v : S' => locHom (S' : Set (HeightOneSpectrum (𝓞 F))) (A' v.1)) fun v => continuous_locHom _ (A' v.1))
    (by
      intro x hx
      simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
      intro v
      have e : resH2 (ρ.comp p) (locHom (S' : Set (HeightOneSpectrum (𝓞 F))) (A' v.1)) (continuous_locHom _ _) (resH2 ρ p hp x) =
          resH2 ρ ((p.comp (toGS Ω _)).comp (Dec (F := F) (A' v.1)).subtype) (h.cont.comp continuous_subtype_val) x := by
        obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl
      refine e.trans ?_
      by_cases hv : v.1 ∈ S
      · exact hx ⟨v.1, hv⟩
      · exact hg_loc l (hA' v.1) K h.isOpen h.idx _ _ (fun g hg => hkill _ hv g.1 hg) ρ hρ x)
  refine ⟨i1, r1, ?_⟩
  have e0 : H0 (ρ.comp p) = H0 ρ := by
    ext m
    exact ⟨fun hm g => by obtain ⟨g, rfl⟩ := hps g; exact hm g, fun hm g => hm (p g)⟩
  rw [e0] at g3
  have s1 : ∑ v : S', n v.1 = ∑ v : S, n v.1 + ∑ q : {v // v ∈ S' ∧ v ∉ S}, n q.1 := by
    rw [Finset.sum_coe_sort S' n, Finset.sum_coe_sort S n, ← Finset.sum_sdiff hSS, add_comm,
      Finset.sum_subtype (S' \ S) (p := fun v => v ∈ S' ∧ v ∉ S) (fun _ => Finset.mem_sdiff) n]
  have s2 := Finset.sum_le_sum (s := Finset.univ) fun q _ => (hq q).2
  change _ + ∑ v : S', n v.1 = _ at tail
  beta_reduce
  change _ + ∑ v : S, n v.1 + _ + _ ≤ _ + ∑ w, finrank k (LinearMap.ker ((ρ.comp p) (toGS Ω _ (c w)) - 1)) +
    finrank k (Loc.H0dual (cycF F Ω l k) ((ρ.comp p).comp (toGS Ω _)))
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.ToZModEqOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem toZMod_cycZ_eq_one_of_cycMod_eq_one (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
    (g : G F Ω) (h : cycMod F Ω l 1 g = 1) :
    PadicInt.toZMod ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have h1 := congrArg Units.val h
  simp only [cycMod, MonoidHom.comp_apply, Units.coe_map, Units.val_one] at h1
  have hk : ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
      RingHom.ker (PadicInt.toZModPow 1 : ℤ_[l] →+* ZMod (l ^ 1)) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    exact h1
  rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hk
  exact hk

theorem UpperTheory.V.GC.gen :
    Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → (∀ v, ∃ s, Φ.om k (Φ.loc v s) ≠ 1) → ∀ v, ∃ (u : Fin (Φ.dv v) → Φ.Gv v) (a₀ : Fin (Φ.dv v)), (∀ a, u a ∈ Φ.Iv v ∧ Φ.Ψ (Φ.loc v (u a)) = 1) ∧ (∀ a, a ≠ a₀ → u a ∈ Φ.Nv v) ∧
    ∀ (B : Type) [CommGroup B] [Finite B], IsPGroup l B → ∀ χ : Φ.Gv v →* B, IsOpen (χ.ker : Set (Φ.Gv v)) → (∀ a, χ (u a) = 1) → ∀ g ∈ Φ.Iv v, χ g = 1 := by
  intro hP F Ω _ _ _ _ _ l _ k _ _ Φ S K π ι A pl e c hL hom v
  have hdv : Φ.dv v = locDeg (pl v) := hL.dv v
  have hmemv : ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal := (hL.loc.mem (pl v)).1 ⟨v, rfl⟩
  have hcyc : ∃ g ∈ Dec (A v), cycMod F Ω l 1 g ≠ 1 := by
    obtain ⟨s, hs⟩ := hom v
    refine ⟨ι v s, ?_, fun h1 => hs ?_⟩
    · rw [← hL.loc.range v]
      exact ⟨s, rfl⟩
    · have h2 := toZMod_cycZ_eq_one_of_cycMod_eq_one F Ω l _ h1
      apply Units.ext
      simp [Fr.Frame.om, hL.loc_eq, hL.eps, h2]
  obtain ⟨u', a₀', hu1, hu2, hu3⟩ := genDec hP.lf hP.lt hP.le F Ω l hL.g.odd (pl v) (A v)
    (hL.loc.isOver v) hmemv hcyc K hL.g.normal hL.g.isOpen hL.g.idx
  let eq : Φ.Gv v ≃* Dec (A v) :=
    (MonoidHom.ofInjective (hL.loc.ι_inj v)).trans (MulEquiv.subgroupCongr (hL.loc.range v))
  have heq : ∀ x, ((eq x : Dec (A v)) : G F Ω) = ι v x := fun x => rfl
  have hcont : Continuous eq := by
    apply continuous_induced_rng.2
    exact hL.loc.cont v
  let h' := hcont.homeoOfEquivCompactToT2 (f := eq.toEquiv)
  refine ⟨fun a => eq.symm (u' (Fin.cast hdv a)), Fin.cast hdv.symm a₀', fun a => ⟨?_, ?_⟩,
    fun a ha => ?_, ?_⟩
  · rw [hL.ine v, Subgroup.mem_comap, ← heq, MulEquiv.apply_symm_apply]
    exact (hu1 _).1
  · rw [hL.loc_eq, ← heq, MulEquiv.apply_symm_apply]
    exact hL.K_Ψ _ (hu1 _).2
  · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hL.ine v, Subgroup.mem_comap, ← heq, MulEquiv.apply_symm_apply]
      exact (hu1 _).1
    · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hL.loc_eq, hL.eps, ← heq,
        MulEquiv.apply_symm_apply]
      refine hu2 _ fun h => ha ?_
      rw [← h]
      ext
      simp
  · intro B _ _ hB χ hχ hu g hg
    let χ' : Dec (A v) →* B := χ.comp eq.symm.toMonoidHom
    have hopen : IsOpen (SetLike.coe χ'.ker) := by
      have hs : SetLike.coe χ'.ker = h'.symm ⁻¹' (SetLike.coe χ.ker) := rfl
      rw [hs]
      exact hχ.preimage h'.symm.continuous
    have hg' : ((eq g : Dec (A v)) : G F Ω) ∈ Ine (A v) := by
      rw [heq]
      rw [hL.ine v] at hg
      exact hg
    have := hu3 B hB χ' hopen (fun a => by simpa [χ'] using hu (Fin.cast hdv.symm a)) (eq g) hg'
    simpa [χ'] using this
end

