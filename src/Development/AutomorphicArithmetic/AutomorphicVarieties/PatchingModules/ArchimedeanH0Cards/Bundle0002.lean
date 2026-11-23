module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.AmMaps
section
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem quotient_multiplication_exact {R : Type} [CommRing R] [IsDomain R] (u v w : R) (hv : v ≠ 0)
    (hw : w = v * u) :
    ∃ (f : (R ⧸ Ideal.span {u}) →ₗ[R] (R ⧸ Ideal.span {w}))
      (g : (R ⧸ Ideal.span {w}) →ₗ[R] (R ⧸ Ideal.span {v})),
      Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
      (∀ x, f (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (v * x)) ∧
      (∀ x, g (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x) := by
  subst hw
  have h1 : Ideal.span {u} ≤ Submodule.comap (LinearMap.mulLeft R v) (Ideal.span {v * u}) := by
    intro x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    show v * (t * u) ∈ Ideal.span {v * u}
    rw [Ideal.mem_span_singleton]
    exact ⟨t, by ring⟩
  have h2 : Ideal.span {v * u} ≤ Submodule.comap (LinearMap.id : R →ₗ[R] R) (Ideal.span {v}) := by
    rw [Submodule.comap_id]
    exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right v u)
  let f := Submodule.mapQ (Ideal.span {u}) (Ideal.span {v * u}) (LinearMap.mulLeft R v) h1
  let g := Submodule.mapQ (Ideal.span {v * u}) (Ideal.span {v}) (LinearMap.id : R →ₗ[R] R) h2
  have hf : ∀ x, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (v * x) := fun x => rfl
  have hg : ∀ x, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun x => rfl
  refine ⟨f, g, ?_, ?_, ?_, fun x => rfl, fun x => rfl⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      rw [hf, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at ha
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      exact (mul_dvd_mul_iff_left hv).mp ha
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [hg, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨Submodule.Quotient.mk t, hf t⟩
      · rintro ⟨a, ha⟩
        induction a using Submodule.Quotient.induction_on with
        | H t =>
          rw [hf, Submodule.Quotient.eq, Ideal.mem_span_singleton] at ha
          obtain ⟨s, hs⟩ := ha
          exact ⟨t - u * s, by linear_combination -hs⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, hg x⟩

theorem UpperTheory.V.Pa.B2.amMaps :
    ∀ (K : Type) [Field K] (e m : ℕ), e ≤ m → ∃ (f : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m - e)}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m})) (g : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ e})) (k : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ e}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m})) (r : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m - e)})), Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧ Function.Injective k ∧ Function.Exact k r ∧ Function.Surjective r ∧ ∀ y, f (r y) = (PowerSeries.X : PowerSeries K) ^ e • y := by
  intro K _ e m h
  have hX : (PowerSeries.X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  obtain ⟨f, g, hfi, hfg, hgs, hf, -⟩ :=
    quotient_multiplication_exact ((PowerSeries.X : PowerSeries K) ^ (m - e)) (PowerSeries.X ^ e) (PowerSeries.X ^ m)
      (pow_ne_zero _ hX) (by rw [← pow_add, Nat.add_sub_cancel' h])
  obtain ⟨k, r, hki, hkr, hrs, -, hr⟩ :=
    quotient_multiplication_exact ((PowerSeries.X : PowerSeries K) ^ e) (PowerSeries.X ^ (m - e)) (PowerSeries.X ^ m)
      (pow_ne_zero _ hX) (by rw [← pow_add, Nat.sub_add_cancel h])
  refine ⟨f, g, k, r, hfi, hfg, hgs, hki, hkr, hrs, fun y => ?_⟩
  induction y using Submodule.Quotient.induction_on with
  | H x => exact (congrArg f (hr x)).trans (hf x)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardKerRangeAlt
section
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem card_ker_range {A V W : Type} [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (f : V →ₗ[A] W) : Nat.card V = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]

private def Zu {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (M : FRep A G) (J : Subgroup G) :
    Submodule A (G → M.X) where
  carrier := {z | z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0}
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨add_mem a1 b1, fun g hg => by rw [Pi.add_apply, a2 g hg, b2 g hg, add_zero]⟩
  smul_mem' := by
    rintro c a ⟨a1, a2⟩
    exact ⟨Submodule.smul_mem _ c a1, fun g hg => by rw [Pi.smul_apply, a2 g hg, smul_zero]⟩

private theorem card_Zu {l : ℕ} [Fact l.Prime] {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (h : UnrCount l G J) (M : FRep A G) (hl : ∀ m : M.X, l • m = 0) (hJ : ∀ g ∈ J, ∀ m, M.ρ g m = m) :
    Finite (Zu M J) ∧ Nat.card (Zu M J) = Nat.card M.X := by
  have hLC : LC M.ρ := by
    intro m
    rw [IsLocallyConstant.iff_continuous]
    exact M.cont.comp (continuous_id.prodMk continuous_const)
  have hJ' : ∀ g ∈ J, M.ρ g = 1 := fun g hg => LinearMap.ext (hJ g hg)
  obtain ⟨hfin, hcard⟩ := h A M.X M.ρ hLC hl hJ'
  have hset : ((Zu M J : Submodule A (G → M.X)) : Set (G → M.X)) =
      {z | z ∈ Zl M.ρ ∧ ∀ g ∈ J, z g = 0} := by
    ext z
    show (z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0) ↔ _
    rw [mem_Z1_iff_cocycle, Set.mem_setOf_eq, mem_Zl, IsLocallyConstant.iff_continuous]
  have e : (Zu M J) ≃ {z | z ∈ Zl M.ρ ∧ ∀ g ∈ J, z g = 0} := Set.equivOfEq hset
  refine ⟨?_, ?_⟩
  · haveI := hfin.to_subtype
    exact Finite.of_equiv _ e.symm
  · rw [Nat.card_congr e, Nat.card_coe_set_eq, hcard]

private def kerRep {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (M M' : FRep A G) (u : M.X →ₗ[A] M'.X)
    (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m)) : FRep A G where
  X := LinearMap.ker u
  ρ := Representation.subrepresentation M.ρ (LinearMap.ker u) (fun g m hm => by
    show u (M.ρ g m) = 0
    rw [hu, LinearMap.mem_ker.1 hm, map_zero])
  cont := Continuous.subtype_mk (M.cont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _

private theorem comp_mem_Zu_of_equivariant {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (M M' : FRep A G) (u : M.X →ₗ[A] M'.X) (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m))
    (z : G → M.X) (hz : z ∈ Zu M J) : (fun g => u (z g)) ∈ Zu M' J := by
  have hz' : z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0 := hz
  have hzc := (mem_Z1_iff_cocycle _ _).1 hz'.1
  show (fun g => u (z g)) ∈ Z1 M'.ρ ∧ ∀ g ∈ J, (fun g => u (z g)) g = 0
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨?_, ?_⟩, ?_⟩
  · exact (continuous_of_discreteTopology (f := u)).comp hzc.1
  · intro g h
    simp only [hzc.2 g h, map_add (f := _), hu]
  · intro g hg
    simp only [hz'.2 g hg, map_zero]

private theorem d0_mem_Zu_of_trivial_on {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (M : FRep A G) (hJ : ∀ g ∈ J, ∀ m, M.ρ g m = m) (m : M.X) : d0 M.ρ m ∈ Zu M J := by
  have hd : ∀ g, d0 M.ρ m g = M.ρ g m - m := fun g => rfl
  show d0 M.ρ m ∈ Z1 M.ρ ∧ ∀ g ∈ J, d0 M.ρ m g = 0
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨?_, ?_⟩, ?_⟩
  · have hc : Continuous fun g => M.ρ g m := M.cont.comp (continuous_id.prodMk continuous_const)
    exact (hc.sub continuous_const).congr (fun g => (hd g).symm)
  · intro g h
    rw [hd, hd, hd, map_sub, map_mul, Module.End.mul_apply]
    abel
  · intro g hg
    rw [hd, hJ g hg, sub_self]

private theorem ker_restrict_mem_Zu_of_comp_zero {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (M M' : FRep A G) (u : M.X →ₗ[A] M'.X) (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m))
    (z : G → M.X) (hz : z ∈ Zu M J) (hk : ∀ g, u (z g) = 0) :
    (fun g => (⟨z g, LinearMap.mem_ker.2 (hk g)⟩ : LinearMap.ker u)) ∈ Zu (kerRep M M' u hu) J := by
  have hz' : z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0 := hz
  have hzc := (mem_Z1_iff_cocycle _ _).1 hz'.1
  show _ ∈ Z1 (kerRep M M' u hu).ρ ∧ _
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨?_, ?_⟩, ?_⟩
  · exact hzc.1.subtype_mk _
  · intro g h
    exact Subtype.ext (hzc.2 g h)
  · intro g hg
    exact Subtype.ext (hz'.2 g hg)

theorem UpperTheory.V.Pa.B2.urOf :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), UnrCount l G J → UrAx l J := by
  intro l _ G _ _ _ J h
  unfold UrAx
  intro A _ M hl hJ
  have memZu : ∀ {N : FRep A G} {z : G → N.X}, z ∈ Zu N J ↔ z ∈ Z1 N.ρ ∧ ∀ g ∈ J, z g = 0 :=
    Iff.rfl
  obtain ⟨hfin, hcZ⟩ := card_Zu h M hl hJ
  refine ⟨?_, ?_⟩
  · have hZ : Zu M J ≤ Z1 M.ρ := fun z hz => (memZu.1 hz).1
    have hres : ∀ w : Z1 M.ρ, resH1 M.ρ J.subtype continuous_subtype_val (Submodule.Quotient.mk w) =
        Submodule.Quotient.mk (restrictCocycles1 M.ρ J.subtype continuous_subtype_val w) := fun w => rfl
    let φ0 : Zu M J →ₗ[A] H1 M.ρ := (Submodule.mkQ _) ∘ₗ Submodule.inclusion hZ
    have hφ0 : ∀ z, φ0 z ∈ H1ur M.ρ J := by
      intro z
      rw [H1ur, LinearMap.mem_ker]
      show resH1 M.ρ J.subtype continuous_subtype_val (Submodule.Quotient.mk (Submodule.inclusion hZ z)) = 0
      rw [hres]
      have hz0 : restrictCocycles1 M.ρ J.subtype continuous_subtype_val (Submodule.inclusion hZ z) = 0 :=
        Subtype.ext (funext fun x => (memZu.1 z.2).2 x x.2)
      rw [hz0, Submodule.Quotient.mk_zero]
    let φ : Zu M J →ₗ[A] H1ur M.ρ J := φ0.codRestrict _ hφ0
    let d : M.X →ₗ[A] Zu M J := (d0 M.ρ).codRestrict _ (d0_mem_Zu_of_trivial_on M hJ)
    have hsurj : Function.Surjective φ := by
      rintro ⟨c, hc⟩
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      rw [H1ur, LinearMap.mem_ker] at hc
      change resH1 M.ρ J.subtype continuous_subtype_val (Submodule.Quotient.mk w) = 0 at hc
      rw [hres, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hc
      obtain ⟨m, hm⟩ := hc
      have hwJ : ∀ g ∈ J, w.1 g = 0 := by
        intro g hg
        have hh := hm ⟨g, hg⟩
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hJ g hg, sub_self] at hh
        exact hh
      refine ⟨⟨w.1, memZu.2 ⟨w.2, hwJ⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
    have hker : LinearMap.ker d = H0 M.ρ := by
      ext m
      rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
      constructor
      · intro hm g
        have hh : M.ρ g m - m = 0 := congrArg (fun z : Zu M J => z.1 g) hm
        exact sub_eq_zero.1 hh
      · intro hm
        apply Subtype.ext
        funext g
        exact (sub_eq_zero.2 (hm g) : M.ρ g m - m = 0)
    have hrange : LinearMap.range d = LinearMap.ker φ := by
      ext z
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨m, rfl⟩
        apply Subtype.ext
        show (Submodule.Quotient.mk (Submodule.inclusion hZ (d m)) : H1 M.ρ) = 0
        apply (Submodule.Quotient.mk_eq_zero (Submodule.comap (Z1 M.ρ).subtype (B1 M.ρ))).2
        show d0 M.ρ m ∈ B1 M.ρ
        exact (mem_coboundaries1 _ _).2 ⟨m, fun g => rfl⟩
      · intro hz
        have hz2 : (Submodule.Quotient.mk (Submodule.inclusion hZ z) : H1 M.ρ) = 0 :=
          congrArg Subtype.val hz
        have hB : z.1 ∈ B1 M.ρ :=
          (Submodule.Quotient.mk_eq_zero (Submodule.comap (Z1 M.ρ).subtype (B1 M.ρ))).1 hz2
        obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hB
        exact ⟨m, Subtype.ext (funext fun g => (hm g).symm)⟩
    have hrφ : Nat.card (LinearMap.range φ) = Nat.card (H1ur M.ρ J) := by
      rw [LinearMap.range_eq_top.2 hsurj]
      exact Nat.card_congr Submodule.topEquiv.toEquiv
    haveI := hfin
    have e1 := card_ker_range d
    have e2 := card_ker_range φ
    rw [hker, hrange] at e1
    rw [hrφ, hcZ, e1] at e2
    have hpos : 0 < Nat.card (LinearMap.ker φ) := Nat.card_pos
    rw [mul_comm] at e2
    exact (Nat.eq_of_mul_eq_mul_left hpos e2).le
  · intro M' u hu hsu y' hy' hy'J
    have hl' : ∀ m : M'.X, l • m = 0 := by
      intro m
      obtain ⟨x, rfl⟩ := hsu m
      rw [← map_nsmul, hl, map_zero]
    have hJ' : ∀ g ∈ J, ∀ m : M'.X, M'.ρ g m = m := by
      intro g hg m
      obtain ⟨x, rfl⟩ := hsu m
      rw [← hu, hJ g hg]
    obtain ⟨hfin', hcZ'⟩ := card_Zu h M' hl' hJ'
    let K := kerRep M M' u hu
    have hlK : ∀ m : K.X, l • m = 0 := fun m => Subtype.ext (hl m.1)
    have hJK : ∀ g ∈ J, ∀ m : K.X, K.ρ g m = m := fun g hg m => Subtype.ext (hJ g hg m.1)
    obtain ⟨-, hcZK⟩ := card_Zu h K hlK hJK
    let ψ : Zu M J →ₗ[A] Zu M' J := ((u.compLeft G) ∘ₗ (Zu M J).subtype).codRestrict _
      (fun z => comp_mem_Zu_of_equivariant M M' u hu z.1 z.2)
    let ι : Zu K J →ₗ[A] Zu M J := (((LinearMap.ker u).subtype.compLeft G) ∘ₗ (Zu K J).subtype).codRestrict _
      (fun w => comp_mem_Zu_of_equivariant K M (LinearMap.ker u).subtype (fun g m => rfl) w.1 w.2)
    have hιinj : Function.Injective ι := by
      intro a b hab
      apply Subtype.ext
      funext g
      exact Subtype.ext (congrArg (fun z : Zu M J => z.1 g) hab)
    have hιr : LinearMap.range ι = LinearMap.ker ψ := by
      ext z
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨w, rfl⟩
        apply Subtype.ext
        funext g
        exact LinearMap.mem_ker.1 (w.1 g).2
      · intro hz
        have hk : ∀ g, u (z.1 g) = 0 := fun g => congrArg (fun y : Zu M' J => y.1 g) hz
        exact ⟨⟨_, ker_restrict_mem_Zu_of_comp_zero M M' u hu z.1 z.2 hk⟩, Subtype.ext rfl⟩
    have hcM : Nat.card M.X = Nat.card K.X * Nat.card M'.X := by
      have e := card_ker_range u
      rw [LinearMap.range_eq_top.2 hsu, Nat.card_congr Submodule.topEquiv.toEquiv] at e
      exact e
    have e2 := card_ker_range ψ
    rw [← hιr, Nat.card_congr (LinearEquiv.ofInjective ι hιinj).symm.toEquiv, hcZ, hcZK, hcM] at e2
    have hposK : 0 < Nat.card K.X := Nat.card_pos
    have hrψ : Nat.card (LinearMap.range ψ) = Nat.card (Zu M' J) := by
      rw [hcZ']
      exact (Nat.eq_of_mul_eq_mul_left hposK e2).symm
    haveI := hfin'
    have htop : (LinearMap.range ψ).toAddSubgroup = ⊤ := AddSubgroup.eq_top_of_card_eq _ hrψ
    have hmem : (⟨y', memZu.2 ⟨hy', hy'J⟩⟩ : Zu M' J) ∈ LinearMap.range ψ := by
      have hh : (⟨y', memZu.2 ⟨hy', hy'J⟩⟩ : Zu M' J) ∈ (LinearMap.range ψ).toAddSubgroup := by
        rw [htop]
        exact AddSubgroup.mem_top _
      exact hh
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hmem
    exact ⟨z.1, (memZu.1 z.2).1, (memZu.1 z.2).2, fun g => congrArg (fun y : Zu M' J => y.1 g) hz⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CohAxIso
section
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

noncomputable section

namespace UpperTheory.V.Pa.B2

section Pull

variable {A Γ Γ' : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']

private def pull (p : Γ →* Γ') (hp : Continuous p) (M : FRep A Γ') : FRep A Γ where
  X := M.X
  ρ := M.ρ.comp p
  cont := M.cont.comp (hp.prodMap continuous_id)

variable (p : Γ ≃* Γ') (hp : Continuous p) (hq : Continuous p.symm) (M : FRep A Γ')

private def r1 : H1 M.ρ →ₗ[A] H1 (pull p.toMonoidHom hp M).ρ :=
  pairH1DecompositionMap M.ρ (pull p.toMonoidHom hp M).ρ p.toMonoidHom hp LinearMap.id continuous_id fun _ _ => rfl

private def r2 : H2 M.ρ →ₗ[A] H2 (pull p.toMonoidHom hp M).ρ :=
  compatiblePairH2 M.ρ (pull p.toMonoidHom hp M).ρ p.toMonoidHom hp LinearMap.id continuous_id fun _ _ => rfl

private theorem back (g : Γ') (m : M.X) : (pull p.toMonoidHom hp M).ρ (p.symm g) m = M.ρ g m := by
  show M.ρ (p.toMonoidHom (p.symm g)) m = M.ρ g m
  simp

include hq in
private theorem restriction_one_bijective : Function.Bijective (r1 p hp M) := by
  let s : H1 (pull p.toMonoidHom hp M).ρ →ₗ[A] H1 M.ρ :=
    pairH1DecompositionMap (pull p.toMonoidHom hp M).ρ M.ρ p.symm.toMonoidHom hq LinearMap.id continuous_id
      fun g m => back p hp M g m
  refine Function.bijective_iff_has_inverse.mpr ⟨s, fun x => ?_, fun x => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r1, pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (p.apply_symm_apply g)
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r1, pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (p.symm_apply_apply g)

include hq in
private theorem restriction_two_bijective : Function.Bijective (r2 p hp M) := by
  let s : H2 (pull p.toMonoidHom hp M).ρ →ₗ[A] H2 M.ρ :=
    compatiblePairH2 (pull p.toMonoidHom hp M).ρ M.ρ p.symm.toMonoidHom hq LinearMap.id continuous_id
      fun g m => back p hp M g m
  refine Function.bijective_iff_has_inverse.mpr ⟨s, fun x => ?_, fun x => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r2, compatiblePairH2, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (Prod.ext (p.apply_symm_apply g.1) (p.apply_symm_apply g.2))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r2, compatiblePairH2, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (Prod.ext (p.symm_apply_apply g.1) (p.symm_apply_apply g.2))

private theorem card_H0_pullback_eq : Nat.card (H0 (pull p.toMonoidHom hp M).ρ) = Nat.card (H0 M.ρ) := by
  have e : H0 (pull p.toMonoidHom hp M).ρ = H0 M.ρ := by
    ext m
    simp only [H0, Representation.mem_invariants]
    constructor
    · intro h g
      rw [← back p hp M g m]
      exact h _
    · intro h g
      exact h (p g)
  rw [e]
  rfl

include hp hq in
private theorem finH_iso (l : ℕ) (h : FinH l Γ) : FinH l Γ' := by
  intro A _ M hl
  obtain ⟨h1, h2⟩ := h A (pull p.toMonoidHom hp M) hl
  exact ⟨Finite.of_equiv _ (Equiv.ofBijective _ (restriction_one_bijective p hp hq M)).symm,
    Finite.of_equiv _ (Equiv.ofBijective _ (restriction_two_bijective p hp hq M)).symm⟩

include hp hq in
private theorem onto_iso (l : ℕ) (h : SecondCohomologyRightExactModL l Γ) : SecondCohomologyRightExactModL l Γ' := by
  intro A _ M M' hl u hu hs y
  have hu' : ∀ (g : Γ) (m : (pull p.toMonoidHom hp M).X),
      u ((pull p.toMonoidHom hp M).ρ g m) = (pull p.toMonoidHom hp M').ρ g (u m) :=
    fun g m => hu (p g) m
  have key : ∀ x, r2 p hp M' (mapH2 M.ρ M'.ρ u continuous_of_discreteTopology hu x) =
      mapH2 (pull p.toMonoidHom hp M).ρ (pull p.toMonoidHom hp M').ρ u continuous_of_discreteTopology hu'
        (r2 p hp M x) := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [r2, compatiblePairH2, mapH2, Submodule.mapQ_apply]
    rfl
  obtain ⟨x', hx'⟩ := h A (pull p.toMonoidHom hp M) (pull p.toMonoidHom hp M') hl u hu' hs (r2 p hp M' y)
  obtain ⟨x, rfl⟩ := (restriction_two_bijective p hp hq M).2 x'
  refine ⟨x, (restriction_two_bijective p hp hq M').1 ?_⟩
  rw [key, hx']

end Pull

section Gl

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (e : G.Hom G') {A : Type} [CommRing A]

private theorem pl_φ (w : (plOf G).ι) (g : (plOf G).G w) : e.p ((plOf G).φ w g) = (plOf G').φ w g := by
  cases w with
  | inl v => exact e.φ v g
  | inr u => exact e.φu u g

private def pullD (D : Dat A (plOf G')) : Dat A (plOf G) where
  M := pull e.p e.cont D.M
  Q w := D.Q w
  π w := D.π w
  surj w := D.surj w
  equiv w g m := by
    have h := D.equiv w g m
    rw [← pl_φ e w g] at h
    exact h

end Gl

end UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.cohAxIso :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (e : G.Hom G') (d : ℕ) (dv : L.Vl → ℕ), Function.Injective e.p → CohAx G d dv → CohAx G' d dv := by
  intro l _ L G G' e d dv hinj hG
  haveI : T2Space G'.Γ := inferInstance
  let q : G.Γ ≃* G'.Γ := MulEquiv.ofBijective e.p ⟨hinj, e.surj⟩
  have hq : Continuous q := e.cont
  have hqs : Continuous q.symm :=
    (Continuous.homeoOfEquivCompactToT2 (f := q.toEquiv) e.cont).symm.continuous
  refine ⟨hG.sum, finH_iso q hq hqs l hG.fin, hG.finV, hG.finU, onto_iso q hq hqs l hG.onto, ?_,
    hG.leV, hG.leU, hG.ur, ?_⟩
  · obtain ⟨c, hc, hf⟩ := hG.ge
    refine ⟨fun i => e.p (c i), fun i => ⟨by rw [e.η]; exact (hc i).1, by rw [← map_mul, (hc i).2, map_one]⟩, ?_⟩
    intro A _ M hl
    have h := hf A (pull q.toMonoidHom hq M) hl
    rw [card_H0_pullback_eq] at h
    rw [Nat.card_congr (Equiv.ofBijective _ (restriction_two_bijective q hq hqs M)),
      Nat.card_congr (Equiv.ofBijective _ (restriction_one_bijective q hq hqs M))]
    exact h
  · intro A _ D hl
    have h := hG.ck A (pullD e D) hl
    have hc : ∀ x, D.loc2 x = (pullD e D).loc2 (r2 q hq D.M x) := by
      intro x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      funext w
      simp only [Dat.loc2, LinearMap.pi_apply, r2, compatiblePairH2, Submodule.mapQ_apply]
      congr 1
      ext y
      show D.π w (z.1 ((plOf G').φ w y.1, (plOf G').φ w y.2)) =
        D.π w (z.1 (e.p ((plOf G).φ w y.1), e.p ((plOf G).φ w y.2)))
      rw [pl_φ e w y.1, pl_φ e w y.2]
    have hr : (pullD e D).loc2.range = D.loc2.range := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨x0, rfl⟩ := (restriction_two_bijective q hq hqs D.M).2 x
        exact ⟨x0, hc x0⟩
      · rintro ⟨x, rfl⟩
        exact ⟨r2 q hq D.M x, (hc x).symm⟩
    have h1 : Nat.card (pullD e D).Ck2 = Nat.card D.Ck2 := by
      show Nat.card (_ ⧸ (pullD e D).loc2.range) = Nat.card (_ ⧸ D.loc2.range)
      rw [hr]
      rfl
    rw [← h1]
    refine h.trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)))
    constructor
    · intro hf g m
      obtain ⟨g0, rfl⟩ := e.surj g
      rw [e.ε]
      exact hf g0 m
    · intro hf g m
      have := hf (e.p g) m
      rw [e.ε] at this
      exact this
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.InV
section
namespace UpperTheory.V.Pa.B2

variable {l : ℕ} [Fact l.Prime] {L : Loc} (G : Glob l L)

def inV (v : L.Vl) : (plOf G).ι := Sum.inl v

def inU (u : L.St) : (plOf G).ι := Sum.inr u

end UpperTheory.V.Pa.B2
end

