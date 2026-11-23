module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem isLocallyConstant_matrix_of_adicCont_of_isNilpotent {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra A R] {n : ℕ} {X : Type}
    [TopologicalSpace X] (t : A) (ht : IsNilpotent (algebraMap A R t)) (z : X → Matrix (Fin n) (Fin n) R)
    (hz : ∀ i j, AdicCont (Ideal.span {(algebraMap A R) t}) fun g => z g i j) : IsLocallyConstant z := by
  obtain ⟨k, hk⟩ := ht
  have hI : Ideal.span {(algebraMap A R) t} ^ k = ⊥ := by
    rw [Ideal.span_singleton_pow, hk, Ideal.span_singleton_eq_bot]
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h2 : ∀ i j, ∀ᶠ y in nhds x, z y i j = z x i j := by
    intro i j
    have := hz i j k
    rw [IsLocallyConstant.iff_eventually_eq] at this
    filter_upwards [this x] with y hy
    rw [Ideal.Quotient.eq, hI, Ideal.mem_bot, sub_eq_zero] at hy
    exact hy
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h2 i)] with y hy
  ext i j
  exact hy i j

private theorem topFG_subgroup_of_finiteIndex_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.FiniteIndex] (hH : IsOpen (H : Set G)) (hG : TopFG G) : TopFG H := by
  obtain ⟨s, hsf, hsd⟩ := hG
  set K := Subgroup.closure s with hK
  have hfgK : Group.FG K := (Subgroup.fg_iff K).2 ⟨s, hK.symm, hsf⟩
  have hfg : Group.FG (H.subgroupOf K) := inferInstance
  obtain ⟨S, hS, hSf⟩ := Group.fg_iff.1 hfg
  let ι : H.subgroupOf K →* H :=
    { toFun := fun x => ⟨((x : K) : G), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨ι '' S, hSf.image _, ?_⟩
  unfold TopGen
  have hr : ((Subgroup.closure (ι '' S) : Subgroup H) : Set H) = Subtype.val ⁻¹' (K : Set G) := by
    rw [← MonoidHom.map_closure, hS, ← MonoidHom.range_eq_map]
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨y, rfl⟩
      exact (y : K).2
    · intro hx
      exact ⟨⟨⟨x, hx⟩, x.2⟩, rfl⟩
  rw [hr]
  exact hsd.preimage hH.isOpenMap_subtype_val

private theorem isLocallyConstant_of_comp_surjective_of_compactSpace {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y]
    (f : X → Y) (hc : Continuous f) (hs : Function.Surjective f) (g : Y → Z)
    (hg : IsLocallyConstant (g ∘ f)) : IsLocallyConstant g := by
  have hq : Topology.IsQuotientMap f := hc.isClosedMap.isQuotientMap hc hs
  intro s
  rw [← hq.isOpen_preimage]
  exact hg s

private theorem t1_lemma {l : ℕ} [Fact l.Prime] {L : Loc} {G0 G1 G2 : Glob l L} (h1 : G1.Hom G0) (h2 : G2.Hom G0)
    {P : Type} [Group P] [TopologicalSpace P] [CompactSpace P] (f1 : P →* G1.G₀) (f2 : P →* G2.G₀)
    (hs : Function.Surjective f1) (hc1 : Continuous f1) (hc2 : Continuous f2) (κ : P → P)
    (hκ1 : ∀ x, f1 (κ x) = G1.frame.conj (f1 x)) (hκ2 : ∀ x, f2 (κ x) = G2.frame.conj (f2 x))
    {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A) (ht : IsNilpotent (algebraMap A R t))
    (ρ : G0.G₀ → Matrix (Fin n) (Fin n) R) (hρ : ∀ x, ρ (h1.p₀ (f1 x)) = ρ (h2.p₀ (f2 x)))
    (w wi : L.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R))
    (z1 : G1.G₀ → Matrix (Fin n) (Fin n) R) (z2 : G2.G₀ → Matrix (Fin n) (Fin n) R)
    (hz : ∀ x, z1 (f1 x) = z2 (f2 x)) (hv : ∀ v g, z1 (G1.φ v g) = z2 (G2.φ v g))
    (hu : ∀ u g, z1 (G1.φu u g) = z2 (G2.φu u g))
    (hm : z2 ∈ SelZ G2.frame t (fun g => ρ (h2.p₀ g)) w wi V) :
    z1 ∈ SelZ G1.frame t (fun g => ρ (h1.p₀ g)) w wi V := by
  simp only [SelZ, Set.mem_setOf_eq] at hm ⊢
  obtain ⟨hV, hA, hcoc, hconj, hU, hL⟩ := hm
  have hz2 : IsLocallyConstant z2 := isLocallyConstant_matrix_of_adicCont_of_isNilpotent t ht z2 hA
  have hz1 : IsLocallyConstant z1 := by
    refine isLocallyConstant_of_comp_surjective_of_compactSpace f1 hc1 hs z1 ?_
    have e : z1 ∘ f1 = z2 ∘ f2 := funext hz
    rw [e]
    exact hz2.comp_continuous hc2
  have pφ : ∀ (G : Glob l L) (h : G.Hom G0) v g, h.p₀ (G.φ v g) = G0.φ v g :=
    fun G h v g => Subtype.ext (h.φ v g)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨x, rfl⟩ := hs g
    rw [hz]
    exact hV _
  · intro i j k
    exact hz1.comp fun m => Ideal.Quotient.mk _ (m i j)
  · intro g h
    obtain ⟨x, rfl⟩ := hs g
    obtain ⟨y, rfl⟩ := hs h
    rw [← map_mul, ← map_inv, hz, hz, hz, hρ, hρ, map_mul, map_inv]
    exact hcoc _ _
  · intro g
    obtain ⟨x, rfl⟩ := hs g
    rw [← hκ1, hz, hz, hκ2]
    exact hconj _
  · intro u g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    rw [hu]
    exact hU u _ (Subgroup.mem_map_of_mem _ hy)
  · intro v
    obtain ⟨Y, hY, hLY⟩ := hL v
    refine ⟨Y, hY, ?_⟩
    unfold LocAt dY at hLY ⊢
    intro g
    have e1 : z1 ((G1.frame.φ v) g) = z2 ((G2.frame.φ v) g) := hv v g
    have e2 : ρ (h1.p₀ ((G1.frame.φ v) g)) = ρ (h2.p₀ ((G2.frame.φ v) g)) := by
      show ρ (h1.p₀ ((G1.φ v) g)) = ρ (h2.p₀ ((G2.φ v) g))
      rw [pφ, pφ]
    have e3 : ρ (h1.p₀ ((G1.frame.φ v) g)⁻¹) = ρ (h2.p₀ ((G2.frame.φ v) g)⁻¹) := by
      show ρ (h1.p₀ ((G1.φ v) g)⁻¹) = ρ (h2.p₀ ((G2.φ v) g)⁻¹)
      rw [← map_inv, ← map_inv, pφ, pφ]
    beta_reduce at hLY ⊢
    rw [e1, e2, e3]
    exact hLY g

theorem UpperTheory.V.Pa.t1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] [Finite R] (t : A) (ρ : G0.G₀ → Matrix (Fin n) (Fin n) R) (w wi : L.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), IsNilpotent (algebraMap A R t) → ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g * ρ h) → IsLocallyConstant ρ → ∀ᶠ N in (Λ.U : Filter ℕ), (∀ g, ρ ((T.h N).p₀ (Λ.π0 N g)) = ρ (Λ.h.p₀ (Λ.πo0 g))) ∧ (∀ z ∈ SelZ Λ.G.frame t (fun g => ρ (Λ.h.p₀ g)) w wi V, ∃ zN ∈ SelZ (T.GN N).frame t (fun g => ρ ((T.h N).p₀ g)) w wi V, Λ.Rel N zN z) ∧ ∀ zN ∈ SelZ (T.GN N).frame t (fun g => ρ ((T.h N).p₀ g)) w wi V, ∃ z ∈ SelZ Λ.G.frame t (fun g => ρ (Λ.h.p₀ g)) w wi V, Λ.Rel N zN z := by
  intro l _ L G0 T Λ n A R _ _ _ _ t ρ w wi V ht h1 hmul hlc
  have hηeq : ∀ N (x : Λ.Ph), (T.GN N).η (Λ.π N x) = Λ.G.η (Λ.πo x) := by
    intro N x
    have hm := T.H_η _ (Λ.modH N x)
    rw [map_mul, map_inv, mul_inv_eq_one, (T.h N).η, Λ.h.η] at hm
    exact hm
  have s0 : ∀ N, Function.Surjective (Λ.π0 N) := by
    intro N y
    obtain ⟨x, hx⟩ := Λ.π_surj N y
    have hmem : x ∈ (Λ.G.η.comp Λ.πo).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hηeq N x, hx]
      exact y.2
    exact ⟨⟨x, hmem⟩, Subtype.ext hx⟩
  have so : Function.Surjective Λ.πo0 := by
    intro y
    obtain ⟨x, hx⟩ := Λ.πo_surj y
    have hmem : x ∈ (Λ.G.η.comp Λ.πo).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hx]
      exact y.2
    exact ⟨⟨x, hmem⟩, Subtype.ext hx⟩
  have c0 : ∀ N, Continuous (Λ.π0 N) := fun N =>
    Continuous.subtype_mk ((Λ.π_cont N).comp continuous_subtype_val) _
  have co : Continuous Λ.πo0 :=
    Continuous.subtype_mk (Λ.πo_cont.comp continuous_subtype_val) _
  have ch : ∀ (G : Glob l L) (h : G.Hom G0), Continuous h.p₀ := fun G h =>
    Continuous.subtype_mk (h.cont.comp continuous_subtype_val) _
  let κ : Λ.Ph0 → Λ.Ph0 := fun x =>
    ⟨Λ.ct * x * Λ.ct⁻¹, (MonoidHom.normal_ker _).conj_mem _ x.2 _⟩
  have hκN : ∀ N x, Λ.π0 N (κ x) = (T.GN N).frame.conj (Λ.π0 N x) := by
    intro N x
    apply Subtype.ext
    show Λ.π N (Λ.ct * x * Λ.ct⁻¹) = (T.GN N).c * Λ.π N x * ((T.GN N).c)⁻¹
    rw [map_mul, map_mul, map_inv, Λ.ct_N]
  have hκo : ∀ x, Λ.πo0 (κ x) = Λ.G.frame.conj (Λ.πo0 x) := by
    intro x
    apply Subtype.ext
    show Λ.πo (Λ.ct * x * Λ.ct⁻¹) = Λ.G.c * Λ.πo x * (Λ.G.c)⁻¹
    rw [map_mul, map_mul, map_inv, Λ.ct_o]
  have hFG : TopFG Λ.Ph0 := by
    refine topFG_subgroup_of_finiteIndex_of_isOpen _ ?_ ?_
    · exact (Λ.G.η_open).preimage Λ.πo_cont
    · obtain ⟨s, hs⟩ := Λ.fg
      refine ⟨s, s.finite_toSet, ?_⟩
      unfold TopGen
      rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hs]
      rfl
  let ρ' : Λ.Ph0 → Matrix (Fin n) (Fin n) R := fun g => ρ (Λ.h.p₀ (Λ.πo0 g))
  have hfin := coc_fin Λ.Ph0 R n ρ' hFG (by simp [ρ', h1]) (by intro g h; simp [ρ', hmul])
    (hlc.comp_continuous ((ch _ _).comp co))
  set C := {z : Λ.Ph0 → Matrix (Fin n) (Fin n) R | IsLocallyConstant z ∧ ∀ (g h : Λ.Ph0), z (g * h) = z g + ρ' g * z h * ρ' g⁻¹} with hC
  let stabR {P Z : Type} [Group P] (c : P → Z) : Subgroup P := {
    carrier := {k | ∀ g, c (g * k) = c g}
    one_mem' g := by rw [mul_one]
    mul_mem' {a b} ha hb g := by rw [← mul_assoc, hb, ha]
    inv_mem' {a} ha g := by
      have := ha (g * a⁻¹)
      rw [inv_mul_cancel_right] at this
      exact this.symm }

  have stabR_open {P Z : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
      (c : P → Z) (hc : IsLocallyConstant c) : IsOpen (stabR c : Set P) := by
    classical
    apply Subgroup.isOpen_of_mem_nhds (g := 1)
    have key : ∀ z ∈ Set.range c, ∀ᶠ k in nhds (1 : P), ∀ g, c g = z → c (g * k) = z := by
      intro z _
      have hK : IsCompact (c ⁻¹' {z}) := (hc.isClosed_fiber z).isCompact
      obtain ⟨V, hV, hKV⟩ := compact_open_separated_mul_right hK (hc.isOpen_fiber z) le_rfl
      filter_upwards [hV] with k hk g hg
      exact hKV (Set.mul_mem_mul hg hk)
    have hall := (Filter.eventually_all_finite hc.range_finite).2 key
    filter_upwards [hall] with k hk
    exact (show ∀ g, c (g * k) = c g from fun g => hk (c g) ⟨g, rfl⟩ g rfl)

  have fac_iff {P A Z : Type} [Group P] [Group A] (f : P →* A) (hf : Function.Surjective f) (c : P → Z) :
      (∃ z : A → Z, ∀ g, z (f g) = c g) ↔ f.ker ≤ stabR c := by
    constructor
    · rintro ⟨z, hz⟩ k hk
      show ∀ g, c (g * k) = c g
      intro g
      rw [← hz, ← hz, map_mul, MonoidHom.mem_ker.1 hk, mul_one]
    · intro hle
      refine ⟨fun a => c (Classical.choose (hf a)), fun g => ?_⟩
      show c (Classical.choose (hf (f g))) = c g
      have hspec : f (Classical.choose (hf (f g))) = f g := Classical.choose_spec (hf (f g))
      generalize Classical.choose (hf (f g)) = g' at hspec ⊢
      have hk : g'⁻¹ * g ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hspec, inv_mul_cancel]
      have := (show ∀ y, c (y * (g'⁻¹ * g)) = c y from hle hk) g'
      rw [mul_inv_cancel_left] at this
      exact this.symm

  have ker_iff {P A : Type} [Group P] [Group A] (H : Subgroup P) (B : Subgroup A) (π : P →* A)
      (f : H →* B) (hf : ∀ g, (f g : A) = π g) (hH : π.ker ≤ H) (S : Subgroup H) :
      f.ker ≤ S ↔ π.ker ≤ (S.map H.subtype).normalCore := by
    have hker : ∀ h : H, h ∈ f.ker ↔ (h : P) ∈ π.ker := by
      intro h
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hf, OneMemClass.coe_eq_one]
    constructor
    · intro hle
      rw [Subgroup.normal_le_normalCore]
      intro k hk
      have hkH : k ∈ H := hH hk
      exact ⟨⟨k, hkH⟩, hle ((hker ⟨k, hkH⟩).2 hk), rfl⟩
    · intro hle h hh
      obtain ⟨s, hs, hsh⟩ := (Subgroup.normalCore_le _) (hle ((hker h).1 hh))
      have : s = h := Subtype.ext hsh
      rw [← this]
      exact hs

  have eventually_factor_through_tower_iff_limit :
      ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (c : Λ.Ph0 → Z), IsLocallyConstant c → ∀ᶠ N in (Λ.U : Filter ℕ), ((∃ zN : (T.GN N).G₀ → Z, ∀ g, zN (Λ.π0 N g) = c g) ↔ ∃ z : Λ.G.G₀ → Z, ∀ g, z (Λ.πo0 g) = c g) := by
    intro l _ L G0 T Λ Z c hc
    set K0 : Subgroup Λ.Ph := (Λ.G.η.comp Λ.πo).ker with hK0def
    have hK0 : IsOpen (K0 : Set Λ.Ph) := Λ.Ph0_open
    haveI : CompactSpace Λ.Ph0 := isCompact_iff_compactSpace.mp (K0.isClosed_of_isOpen hK0).isCompact
    have hS : IsOpen (stabR c : Set Λ.Ph0) := stabR_open c hc
    have hO : IsOpen (((stabR c).map K0.subtype : Subgroup Λ.Ph) : Set Λ.Ph) := by
      rw [Subgroup.coe_map]
      exact hK0.isOpenMap_subtype_val _ hS
    let O : OpenSubgroup Λ.Ph := ⟨(stabR c).map K0.subtype, hO⟩
    haveI : Finite (Λ.Ph ⧸ O.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hO
    haveI : O.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    let V : OpenNormalSubgroup Λ.Ph :=
      { toSubgroup := O.toSubgroup.normalCore
        isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (O.toSubgroup.normalCore_isClosed O.isClosed) }
    have hHo : Λ.πo.ker ≤ K0 := by
      intro k hk
      rw [hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
    filter_upwards [Λ.ker_lim V] with N hN
    have hHN : (Λ.π N).ker ≤ K0 := by
      intro k hk
      rw [hK0def, MonoidHom.mem_ker, MonoidHom.comp_apply, ← Λ.η_π N, MonoidHom.mem_ker.1 hk, map_one]
    rw [fac_iff _ (Λ.π0_surj N), fac_iff _ Λ.πo0_surj,
      ker_iff K0 _ (Λ.π N) (Λ.π0 N) (fun g => rfl) hHN, ker_iff K0 _ Λ.πo Λ.πo0 (fun g => rfl) hHo]
    have e : (Λ.π N).ker ⊔ ((stabR c).map K0.subtype).normalCore =
        Λ.πo.ker ⊔ ((stabR c).map K0.subtype).normalCore := hN
    rw [← sup_eq_right, e, sup_eq_right]
  have exists_open_normal {P Z : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
      [TotallyDisconnectedSpace P] (K : Subgroup P) (hK : IsOpen (K : Set P)) (c : K → Z) (hc : IsLocallyConstant c) :
      ∃ V : OpenNormalSubgroup P, ∀ g g' : K, (g : P)⁻¹ * g' ∈ V → c g = c g' := by
    have hKc : IsClosed (K : Set P) := Subgroup.isClosed_of_isOpen K hK
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
    have hfin : (Set.range c).Finite := hc.range_finite
    have hS : ∀ z, ∃ W ∈ nhds (1 : P), ∀ x ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P), ∀ w ∈ W,
        x * w ∈ (Subtype.val '' (c ⁻¹' {z}) : Set P) := by
      intro z
      have hcpt : IsCompact (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
        (hc.isClosed_fiber z).isCompact.image continuous_subtype_val
      have ho : IsOpen (Subtype.val '' (c ⁻¹' {z}) : Set P) :=
        hK.isOpenMap_subtype_val _ (hc.isOpen_fiber z)
      open scoped Pointwise in
      obtain ⟨W, hW, hWS⟩ := compact_open_separated_mul_right hcpt ho subset_rfl
      open scoped Pointwise in
      exact ⟨W, hW, fun x hx w hw => hWS (Set.mul_mem_mul hx hw)⟩
    choose W hW hWS using hS
    have hI : (⋂ z ∈ Set.range c, W z) ∈ nhds (1 : P) := (Filter.biInter_mem hfin).2 fun z _ => hW z
    obtain ⟨O, hOI, hOo, h1O⟩ := mem_nhds_iff.1 hI
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
    refine ⟨H, fun g g' hgg => ?_⟩
    have h1 : (g : P)⁻¹ * g' ∈ W (c g) := Set.mem_iInter₂.1 (hOI (hH hgg)) (c g) ⟨g, rfl⟩
    have h2 : (g : P) ∈ Subtype.val '' (c ⁻¹' {c g}) := ⟨g, rfl, rfl⟩
    have h3 := hWS (c g) _ h2 _ h1
    rw [mul_inv_cancel_left] at h3
    obtain ⟨a', ha', he⟩ := h3
    have e : a' = g' := Subtype.ext he
    rw [← e]
    exact ha'.symm

  have eventually_factorization_compatible_with_local_maps :
      ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (c : Λ.Ph0 → Z), IsLocallyConstant c → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ (zN : (T.GN N).G₀ → Z) (z : Λ.G.G₀ → Z), (∀ g, zN (Λ.π0 N g) = c g) → (∀ g, z (Λ.πo0 g) = c g) → (∀ v g, zN ((T.GN N).φ v g) = z (Λ.G.φ v g)) ∧ (∀ w g, zN ((T.GN N).φu w g) = z (Λ.G.φu w g)) ∧ ∀ j, zN (T.ph N j) = z (Λ.ph j) ∧ zN (T.ta N j) = z (Λ.ta j) := by
    intro l _ L G0 T Λ Z c hc
    obtain ⟨V, hV⟩ := exists_open_normal _ Λ.Ph0_open c hc
    filter_upwards [Λ.φ_lim V, Λ.φu_lim V, Λ.ph_lim V, Λ.ta_lim V] with N h1 h2 h3 h4 zN z hN ho
    have key : ∀ (a : (T.GN N).G₀) (b : Λ.G.G₀), Close (Λ.π N) Λ.πo V.toSubgroup (a : (T.GN N).Γ) (b : Λ.G.Γ) →
        zN a = z b := by
      rintro a b ⟨g, g', ea, eb, hg⟩
      have m : g ∈ (Λ.G.η.comp Λ.πo).ker := (Λ.η_π N g).symm.trans (by rw [ea]; exact a.2)
      have m' : g' ∈ (Λ.G.η.comp Λ.πo).ker := show Λ.G.η (Λ.πo g') = 1 by rw [eb]; exact b.2
      have ea' : a = Λ.π0 N ⟨g, m⟩ := Subtype.ext ea.symm
      have eb' : b = Λ.πo0 ⟨g', m'⟩ := Subtype.ext eb.symm
      rw [ea', eb', hN, ho]
      exact hV _ _ hg
    exact ⟨fun v g => key _ _ (h1 v g), fun w g => key _ _ (h2 w g), fun j => ⟨key _ _ (h3 j), key _ _ (h4 j)⟩⟩
  have eventually_locallyConstant_comp_tower_eq :
      ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (Z : Type) (ρ : G0.G₀ → Z), IsLocallyConstant ρ → ∀ᶠ N in (Λ.U : Filter ℕ), ∀ g, ρ ((T.h N).p₀ (Λ.π0 N g)) = ρ (Λ.h.p₀ (Λ.πo0 g)) := by
    intro l _ L G0 T Λ Z ρ hρ
    have hKo : IsOpen ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := G0.η_open
    have hKc : IsClosed ((G0.η.ker : Subgroup G0.Γ) : Set G0.Γ) := Subgroup.isClosed_of_isOpen _ hKo
    haveI : CompactSpace G0.G₀ := isCompact_iff_compactSpace.mp hKc.isCompact
    have hfin : (Set.range ρ).Finite := hρ.range_finite
    have hS : ∀ z, ∃ V ∈ nhds (1 : G0.Γ), ∀ v ∈ V, ∀ x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ),
        v * x ∈ (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) := by
      intro z
      have hc : IsCompact (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
        (hρ.isClosed_fiber z).isCompact.image continuous_subtype_val
      have ho : IsOpen (Subtype.val '' (ρ ⁻¹' {z}) : Set G0.Γ) :=
        hKo.isOpenMap_subtype_val _ (hρ.isOpen_fiber z)
      open scoped Pointwise in
      obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hc ho subset_rfl
      open scoped Pointwise in
      exact ⟨V, hV, fun v hv x hx => hVS (Set.mul_mem_mul hv hx)⟩
    choose V hV hVS using hS
    have hW : (⋂ z ∈ Set.range ρ, V z) ∈ nhds (1 : G0.Γ) := (Filter.biInter_mem hfin).2 fun z _ => hV z
    obtain ⟨O, hOW, hOo, h1O⟩ := mem_nhds_iff.1 hW
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
    refine (Λ.p_lim H).mono ?_
    intro N hN g
    set a := (T.h N).p₀ (Λ.π0 N g)
    set b := Λ.h.p₀ (Λ.πo0 g)
    have hab : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ (H : Set G0.Γ) := hN g.1
    have h1 : (a : G0.Γ) * (b : G0.Γ)⁻¹ ∈ V (ρ b) := Set.mem_iInter₂.1 (hOW (hH hab)) (ρ b) ⟨b, rfl⟩
    have h2 : (b : G0.Γ) ∈ Subtype.val '' (ρ ⁻¹' {ρ b}) := ⟨b, rfl, rfl⟩
    have h3 := hVS (ρ b) _ h1 _ h2
    rw [inv_mul_cancel_right] at h3
    obtain ⟨a', ha', he⟩ := h3
    have e : a' = a := Subtype.ext he
    rw [← e]
    exact ha'
  have hall := (Filter.eventually_all_finite hfin).2 fun c (hc : c ∈ C) =>
    (eventually_factor_through_tower_iff_limit l L G0 T Λ _ c hc.1).and (eventually_factorization_compatible_with_local_maps l L G0 T Λ _ c hc.1)
  filter_upwards [eventually_locallyConstant_comp_tower_eq l L G0 T Λ _ ρ hlc, hall] with N hact hcs
  refine ⟨hact, ?_, ?_⟩
  · intro z hz
    have zlc : IsLocallyConstant z := by
      simp only [SelZ, Set.mem_setOf_eq] at hz
      exact isLocallyConstant_matrix_of_adicCont_of_isNilpotent t ht z hz.2.1
    have hcm : (fun g => z (Λ.πo0 g)) ∈ C := by
      refine ⟨zlc.comp_continuous co, ?_⟩
      intro g h
      simp only [SelZ, Set.mem_setOf_eq] at hz
      show z (Λ.πo0 (g * h)) = z (Λ.πo0 g) + ρ (Λ.h.p₀ (Λ.πo0 g)) * z (Λ.πo0 h) * ρ (Λ.h.p₀ (Λ.πo0 g⁻¹))
      rw [map_mul, hz.2.2.1, map_inv Λ.πo0 g]
    obtain ⟨hd, hl⟩ := hcs _ hcm
    obtain ⟨zN, hzN⟩ := hd.2 ⟨z, fun g => rfl⟩
    refine ⟨zN, ?_, hzN⟩
    obtain ⟨hv, hu, -⟩ := hl zN z hzN (fun g => rfl)
    exact t1_lemma (T.h N) Λ.h (Λ.π0 N) Λ.πo0 (s0 N) (c0 N) co κ (hκN N) hκo t ht ρ hact w wi V zN z hzN hv hu hz
  · intro zN hzN
    have zlc : IsLocallyConstant zN := by
      simp only [SelZ, Set.mem_setOf_eq] at hzN
      exact isLocallyConstant_matrix_of_adicCont_of_isNilpotent t ht zN hzN.2.1
    have hcm : (fun g => zN (Λ.π0 N g)) ∈ C := by
      refine ⟨zlc.comp_continuous (c0 N), ?_⟩
      intro g h
      simp only [SelZ, Set.mem_setOf_eq] at hzN
      show zN (Λ.π0 N (g * h)) = zN (Λ.π0 N g) + ρ (Λ.h.p₀ (Λ.πo0 g)) * zN (Λ.π0 N h) * ρ (Λ.h.p₀ (Λ.πo0 g⁻¹))
      rw [map_mul, hzN.2.2.1, ← map_inv (Λ.π0 N) g, hact, hact]
    obtain ⟨hd, hl⟩ := hcs _ hcm
    obtain ⟨z, hz⟩ := hd.1 ⟨zN, fun g => rfl⟩
    refine ⟨z, ?_, fun g => (hz g).symm⟩
    obtain ⟨hv, hu, -⟩ := hl zN z (fun g => rfl) hz
    exact t1_lemma Λ.h (T.h N) Λ.πo0 (Λ.π0 N) so co (c0 N) κ hκo (hκN N) t ht ρ (fun x => (hact x).symm) w wi V
      z zN hz (fun v g => (hv v g).symm) (fun u g => (hu u g).symm) hzN
