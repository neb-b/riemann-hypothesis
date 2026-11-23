module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FixBdQZero

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.Descend
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem pow_mem_of_PL (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) (V : Set Γ) (hV : IsOpen V) (hle : (PL l H : Set Γ) ⊆ V) : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ V := by
  let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U}
  haveI : Nonempty ι := ⟨⟨⟨⊤, Subgroup.normal_top⟩, fun h _ => ⟨0, trivial⟩⟩⟩
  have hd : Directed (· ⊇ ·) fun U : ι => (U.1 : Set Γ) := by
    intro U U'
    refine ⟨⟨U.1 ⊓ U'.1, fun h hh => ?_⟩, fun a ha => ha.1, fun a ha => ha.2⟩
    obtain ⟨e, he⟩ := U.2 h hh
    obtain ⟨e', he'⟩ := U'.2 h hh
    refine ⟨e + e', ?_, ?_⟩
    · rw [pow_add, pow_mul]
      exact U.1.toSubgroup.pow_mem he _
    · rw [pow_add, mul_comm, pow_mul]
      exact U'.1.toSubgroup.pow_mem he' _
  have hs : Vᶜ ∩ ⋂ U : ι, (U.1 : Set Γ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun a ha => ha.1 (hle ?_)
    have := Set.mem_iInter.1 ha.2
    simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf]
    exact fun U hU => this ⟨U, hU⟩
  obtain ⟨U, hU⟩ := hV.isClosed_compl.isCompact.elim_directed_family_closed (fun U : ι => (U.1 : Set Γ))
    (fun U => U.1.toOpenSubgroup.isClosed) (Set.disjoint_iff_inter_eq_empty.mpr hs) hd
  intro h hh
  obtain ⟨e, he⟩ := U.2 h hh
  refine ⟨e, ?_⟩
  by_contra hn
  exact Set.disjoint_left.1 hU hn he

private theorem affine_ker {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M) (hρ : LC ρ) (y : Γ → M) (hy : y ∈ Zl ρ) :
    ∃ U : OpenNormalSubgroup Γ, ∀ g, g ∈ U ↔ ρ g = 1 ∧ y g = 0 := by
  obtain ⟨h1, h2⟩ := hy
  have y1 : y 1 = 0 := by simpa using h2 1 1
  let a : Γ →* Function.End M :=
    { toFun := fun g m => y g + ρ g m
      map_one' := funext fun m => by simp [y1]; rfl
      map_mul' := fun g h => funext fun m => by
        show _ = y g + ρ g (y h + ρ h m)
        rw [h2, map_mul, map_add (f := _), add_assoc]; rfl }
  have key : ∀ g, g ∈ a.ker ↔ ρ g = 1 ∧ y g = 0 := by
    intro g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : ∀ m, y g + ρ g m = m := congrFun h
      have h0 : y g = 0 := by simpa using h' 0
      exact ⟨LinearMap.ext fun m => by simpa [h0] using h' m, h0⟩
    · rintro ⟨e1, e2⟩
      funext m
      show y g + ρ g m = m
      simp [e1, e2]
  have ho : IsOpen (a.ker : Set Γ) := by
    have : (a.ker : Set Γ) = (⋂ m, {g | ρ g m = m}) ∩ {g | y g = 0} := by
      ext g
      simp only [SetLike.mem_coe, key, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      exact and_congr_left' ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [this]
    exact (isOpen_iInter_of_finite fun m => (hρ m).isOpen_fiber m).inter (h1.isOpen_fiber 0)
  exact ⟨⟨⟨a.ker, ho⟩, MonoidHom.normal_ker a⟩, key⟩

private theorem cocycle_pow {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (y : Γ → M) (hy : y ∈ Zl ρ) (g : Γ) (hg : ρ g = 1) (k : ℕ) :
    y (g ^ k) = k • y g := by
  induction k with
  | zero => simpa using hy.2 1 1
  | succ k ih => rw [pow_succ', hy.2, hg, ih, succ_nsmul']; rfl

private theorem factor_lc {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] [T2Space Γ'] [AddCommGroup M] [Module R M] (ρ : Representation R Γ M)
    (y : Γ → M) (hy : y ∈ Zl ρ) (p : Γ →* Γ') (hc : Continuous p) (hs : Function.Surjective p)
    (hk : ∀ g ∈ p.ker, y g = 0) : ∃ Z : Γ' → M, IsLocallyConstant Z ∧ ∀ g, y g = Z (p g) := by
  have e : ∀ g, y g = y (Function.surjInv hs (p g)) := by
    intro g
    have : g⁻¹ * Function.surjInv hs (p g) ∈ p.ker := by
      rw [MonoidHom.mem_ker, map_mul, Function.surjInv_eq hs, map_inv, inv_mul_cancel]
    have h := hy.2 g (g⁻¹ * Function.surjInv hs (p g))
    rw [hk _ this, map_zero, add_zero, mul_inv_cancel_left] at h
    exact h.symm
  refine ⟨fun γ => y (Function.surjInv hs γ), fun s => ?_, e⟩
  have hq : Topology.IsQuotientMap p := hc.isClosedMap.isQuotientMap hc hs
  rw [← hq.isOpen_preimage]
  convert hy.1 s using 1
  ext g
  simp only [Set.mem_preimage, ← e g]

private theorem epM_mul {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * DD.epM Z = 0 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  ext <;> simp [DD.epM]

private theorem one_add_pow {S : Type} [Ring S] (E : S) (h : E * E = 0) (k : ℕ) : (1 + E) ^ k = 1 + k • E := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc k E E, h, succ_nsmul]; simp; abel

private theorem rho1_pow_eq_one_pro_l (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n)
    (k : Kap x) (m : ℕ) (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) (g : G0.G₀)
    (hg : (g : G0.Γ) ∈ T.H) : ∃ e : ℕ, k.ρ1 (x.Am m) (g ^ l ^ e) = 1 := by
  have hI : IsLocalRing.maximalIdeal x.A ^ m = Ideal.span {x.t ^ m} := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow]
  have h0 : ∀ i j, IsLocallyConstant fun g : G0.G₀ => x.ρX (DD (x.Am m) k.g) g i j := fun i j =>
    ((x.cont i j m).comp (Ideal.Quotient.factor hI.le)).comp (DD.C : x.Am m →+* DD (x.Am m) k.g)
  have ho : IsOpen {g : G0.G₀ | x.ρX (DD (x.Am m) k.g) g = 1} := by
    have : {g : G0.G₀ | x.ρX (DD (x.Am m) k.g) g = 1} = ⋂ i, ⋂ j,
        {g : G0.G₀ | x.ρX (DD (x.Am m) k.g) g i j = (1 : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) i j} := by
      ext g
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Matrix.ext_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (h0 i j).isOpen_fiber _
  obtain ⟨e, g', h1, h2⟩ := pow_mem_of_PL l T.H.toSubgroup _ (G0.η_open.isOpenMap_subtype_val _ ho) (fun a ha => by
    have hη : a ∈ G0.η.ker := by
      have ha' := ha
      simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf] at ha'
      exact ha' ⟨⟨G0.η.ker, G0.η_open⟩, MonoidHom.normal_ker _⟩ fun h hh =>
        ⟨0, by rw [pow_zero, pow_one]; exact T.H_η h hh⟩
    refine ⟨⟨a, hη⟩, ?_, rfl⟩
    show x.ρX _ _ = 1
    rw [NP.ρX]
    simp [mat, hPL ⟨a, hη⟩ ha]) g hg
  have h3 : g' = g ^ l ^ e := Subtype.ext h2
  subst h3
  obtain ⟨r1, r2, -⟩ := rho1 l G0.frame n x k (x.Am m)
  have hp : ∀ (u : G0.G₀) (j : ℕ), k.ρ1 (x.Am m) (u ^ j) = k.ρ1 (x.Am m) u ^ j := fun u j => by
    induction j with
    | zero => rw [pow_zero, pow_zero]; exact r1
    | succ j ih => rw [pow_succ, pow_succ, ← ih]; exact r2 _ _
  refine ⟨e + 1, ?_⟩
  have h1' : x.ρX (DD (x.Am m) k.g) (g ^ l ^ e) = 1 := h1
  rw [pow_succ, pow_mul, hp, Kap.ρ1, h1', mul_one, one_add_pow _ (epM_mul _), add_eq_left]
  exact Matrix.ext fun i j => (finAm l G0.frame n x m k.g).2.2.2.2.1 _

private theorem epsD_one (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n)
    (k : Kap x) (m : ℕ) (g : F.Γ) (hg : PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1) : epsD k (x.Am m) g = 1 := by
  have hl : (l : DD (x.Am m) k.g) = 0 := by
    have := (finAm l F n x m k.g).2.2.2.2.1 1
    rwa [nsmul_eq_mul, mul_one] at this
  have : ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, RingHom.map_sub, hg, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  obtain ⟨c, hc⟩ := this
  rw [epsD, eq_add_of_sub_eq hc]
  simp [hl]

theorem UpperTheory.V.Pa.descend :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m N : ℕ) (rep' : Representation x.A (T.GN N).Γ (k.EpsilonEtaTensorDual (x.Am m))), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → IsAd (T.GN N).frame (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun g => epsD k (x.Am m) ((T.h N).p g)) (k.EpsilonEtaTensorDual (x.Am m)) rep' → ∀ y ∈ Zl rep', y (T.GN N).c = 0 → (∀ j, y (T.ta N j) = 0) → ∃ z ∈ TwZ k (x.Am m), ∀ g : (T.GN N).G₀, (y g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) = z ((T.h N).p₀ g) := by
  intro l _ L G0 T n x k m N rep' hPL had y hy hc hta
  obtain ⟨-, -, f1, -, f2, -, f3, -⟩ := finAm l G0.frame n x m k.g
  obtain ⟨r1, r2, -⟩ := rho1 l G0.frame n x k (x.Am m)
  obtain ⟨-, c2, c3⟩ := lc1 l L (T.GN N) G0 (T.h N) n x k m
  obtain ⟨U, hU⟩ := affine_ker rep' (c3 _ _ rep' c2 had) y hy
  have htriv : ∀ g : (T.GN N).G₀, (T.h N).p g ∈ T.H → k.ρ1 (x.Am m) ((T.h N).p₀ g) = 1 → rep' g = 1 := by
    intro g hg h1
    have h2 : k.ρ1 (x.Am m) ((T.h N).p₀ g⁻¹) = 1 := by
      have := r2 ((T.h N).p₀ g) ((T.h N).p₀ g⁻¹)
      rw [h1, one_mul] at this
      rw [← this, ← map_mul, mul_inv_cancel, map_one]
      exact r1
    refine LinearMap.ext fun Z => Subtype.ext ((had.1 g Z).trans ?_)
    simp only []
    rw [h1, h2, epsD_one l G0.frame n x k m _ (T.H_ε _ hg), one_smul, one_mul, mul_one]
    rfl
  have hker : (T.h N).p.ker ≤ U.toSubgroup := by
    refine (T.ker_le N).trans (Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) U.toOpenSubgroup.isClosed)
    · haveI := U.isNormal'
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨j, rfl⟩
      refine (hU _).2 ⟨htriv _ (by rw [T.ta_ker]; exact T.H.toSubgroup.one_mem) ?_, hta j⟩
      have : (T.h N).p₀ (T.ta N j) = 1 := Subtype.ext (T.ta_ker N j)
      rw [this]
      exact r1
    · refine iInf₂_le U fun h hh => ?_
      have hη : h ∈ (T.GN N).η.ker := by
        rw [MonoidHom.mem_ker, ← (T.h N).η]
        exact T.H_η _ hh
      obtain ⟨e, he⟩ := rho1_pow_eq_one_pro_l l L G0 T n x k m hPL ((T.h N).p₀ ⟨h, hη⟩) hh
      have h1 : rep' (h ^ l ^ e) = 1 := htriv (⟨h, hη⟩ ^ l ^ e)
        ((T.H.toSubgroup.comap (T.h N).p).pow_mem hh _) (by rw [map_pow]; exact he)
      refine ⟨e + 1, (hU _).2 ⟨?_, ?_⟩⟩
      · rw [pow_succ, pow_mul, map_pow, h1, one_pow]
      · rw [pow_succ, pow_mul, cocycle_pow rep' y hy _ h1]
        exact Subtype.ext (Matrix.ext fun i j => f2 _)
  obtain ⟨Z, z1, z2⟩ := factor_lc rep' y hy (T.h N).p (T.h N).cont (T.h N).surj fun g hg => ((hU g).1 (hker hg)).2
  have hs : ∀ g0 : G0.G₀, ∃ g : (T.GN N).G₀, (T.h N).p₀ g = g0 := by
    intro g0
    obtain ⟨g, hg⟩ := (T.h N).surj g0
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    rw [MonoidHom.mem_ker, ← (T.h N).η, hg]
    exact g0.2
  have z3 : ∀ g : (T.GN N).G₀, Z ((T.h N).p₀ g : G0.G₀) = y g := fun g => (z2 g).symm
  refine ⟨fun g0 => Z g0, ⟨fun g => (Z g).2, fun i j => ?_, fun g0 h0 => ?_, fun g0 => ?_⟩, fun g => by rw [← z3]⟩
  · exact (adicLC _ _ _ m _ f3).2 ((z1.comp_continuous continuous_subtype_val).comp fun W => W.1 i j)
  · obtain ⟨g, rfl⟩ := hs g0
    obtain ⟨h, rfl⟩ := hs h0
    have e := congrArg Subtype.val (hy.2 g h)
    rw [Submodule.coe_add, had.1 g] at e
    simp only []
    rw [← map_mul, z3, z3, z3, ← map_inv]
    exact e
  · obtain ⟨g, rfl⟩ := hs g0
    have e := ((polZ l (T.GN N).frame _ _ n _ _ _ rep' had).2 y hy hc).1 g
    have e2 : G0.frame.conj ((T.h N).p₀ g) = (T.h N).p₀ ((T.GN N).frame.conj g) := by
      refine Subtype.ext ?_
      show G0.c * (T.h N).p g * G0.c⁻¹ = (T.h N).p ((T.GN N).c * g * (T.GN N).c⁻¹)
      rw [map_mul, map_mul, map_inv, (T.h N).c]
    simp only []
    rw [e2, z3, z3]
    refine e.trans ?_
    show -(epsD k (x.Am m) ((T.h N).p (T.GN N).c) • _) = _
    rw [(T.h N).c]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FinTwLc
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem finTw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  have hs : ∀ i j, ∀ x, ∀ᶠ y in nhds x, f y i j = f x i j := fun i j =>
    (IsLocallyConstant.iff_eventually_eq _).1 (h i j)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hall : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    exact fun i j => hs i j x
  filter_upwards [hall] with y hy
  ext i j
  exact hy i j

theorem UpperTheory.V.Pa.finTw :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), PhiCond G0.Γ l → (TwZ k (x.Am m)).Finite := by
  intro l _ L G0 n x k m hΦ
  obtain ⟨_, _, hfinR, _, hlR, _, htR, _, _⟩ := finAm l G0.frame n x m k.g
  let χ : G0.Γ →* x.A := (algebraMap ℤ_[l] x.A).toMonoidHom.comp ((Units.coeHom ℤ_[l]).comp G0.ε)
  have hok := (ok1 l L G0 G0 (Glob.Hom.refl G0) n x k (x.Am m) χ).2.1
  obtain ⟨rep, hrep⟩ := adEx l G0.frame x.A (DD (x.Am m) k.g) n _ _ _ hok
  obtain ⟨_, hlce, hLC⟩ := lc1 l L G0 G0 (Glob.Hom.refl G0) n x k m
  have hLCrep := hLC _ _ rep hlce hrep
  haveI : Finite (DD (x.Am m) k.g) := hfinR
  have hl : ∀ v : pairedDualFirstOrderDualMatrixSpace n x.A (x.Am m) k.g x.a, l • v = 0 := by
    intro v
    apply Subtype.ext
    funext i j
    simp [hlR]
  have finite_addMonoidHom_zmod_of_finite (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Finite M] :
      Finite (M →+ ZMod l) := by
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    exact Finite.of_injective (fun f : M →+ ZMod l => (f : M → ZMod l)) DFunLike.coe_injective
  
  have eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (hl : ∀ m : M, l • m = 0)
      (m : M) (h : ∀ f : M →+ ZMod l, f m = 0) : m = 0 := by
    letI : Module (ZMod l) M := AddCommGroup.zmodModule hl
    let b := Module.Basis.ofVectorSpace (ZMod l) M
    apply b.repr.injective
    ext i
    have := h (b.coord i).toAddMonoidHom
    rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
    simpa using this
  have finZ_local : ∀ (l : ℕ) [Fact l.Prime] (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond Γ l → LC ρ → (∀ m : M, l • m = 0) → Finite (Zl ρ) := by
    intro l _ R Γ M _ _ _ _ _ _ _ _ ρ hΦ hρ hl
    let N : Subgroup Γ :=
      { carrier := {g | ∀ m, ρ g m = m}
        mul_mem' := by
          intro a b ha hb m
          simp only [Set.mem_setOf_eq] at ha hb
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by
          intro m
          simp
        inv_mem' := by
          intro a ha m
          simp only [Set.mem_setOf_eq] at ha
          have h1 := ha (ρ a⁻¹ m)
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
          exact h1.symm }
    have hN : IsOpen (N : Set Γ) := by
      have hset : (N : Set Γ) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
        ext g
        simp [N]
      rw [hset]
      exact isOpen_iInter_of_finite (fun m => (hρ m).isOpen_fiber m)
    haveI : Finite (Γ ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
    haveI : Finite (M →+ ZMod l) := finite_addMonoidHom_zmod_of_finite l M
    haveI := hΦ N hN
    have z1 : ∀ z ∈ Zl ρ, z 1 = 0 := by
      intro z hz
      have h := ((mem_Zl ρ).1 hz).2 1 1
      simpa using h
    have zN : ∀ z ∈ Zl ρ, ∀ a b : Γ, a ∈ N → z (a * b) = z a + z b := by
      intro z hz a b ha
      rw [((mem_Zl ρ).1 hz).2, ha]
    refine Finite.of_injective
      (β := (Γ ⧸ N → M) × ((M →+ ZMod l) →
        {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}))
      (fun z => (fun q => z.1 q.out, fun f =>
        ⟨⟨⟨fun k => Multiplicative.ofAdd (f (z.1 k)), ?_⟩, ?_⟩, ?_⟩)) ?_
    · show Multiplicative.ofAdd (f (z.1 ((1 : N) : Γ))) = 1
      rw [Subgroup.coe_one, z1 _ z.2, map_zero, ofAdd_zero]
    · intro k k'
      show Multiplicative.ofAdd (f (z.1 ((k * k' : N) : Γ))) =
        Multiplicative.ofAdd (f (z.1 k)) * Multiplicative.ofAdd (f (z.1 k'))
      rw [Subgroup.coe_mul, zN _ z.2 _ _ k.2, map_add (f := _), ofAdd_add]
    · have hlc : IsLocallyConstant (fun k : N => Multiplicative.ofAdd (f (z.1 k))) :=
        (((mem_Zl ρ).1 z.2).1.comp_continuous continuous_subtype_val).comp _
      rw [MonoidHom.coe_ker]
      exact hlc.isOpen_fiber 1
    · intro z z' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      apply Subtype.ext
      funext g
      have key : ∀ k : N, z.1 k = z'.1 k := by
        intro k
        have hf : ∀ f : M →+ ZMod l, f (z.1 k - z'.1 k) = 0 := by
          intro f
          have h3 := congrArg (fun ψ : {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)} =>
            Multiplicative.toAdd (ψ.1 k)) (congrFun h2 f)
          simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h3
          rw [map_sub, h3, sub_self]
        exact sub_eq_zero.1 (eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul l M hl _ hf)
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N g
      have hg : g = (QuotientGroup.mk g : Γ ⧸ N).out * ((k⁻¹ : N) : Γ) := by
        rw [hk]
        simp [mul_assoc]
      have h1' : z.1 (QuotientGroup.mk g : Γ ⧸ N).out = z'.1 (QuotientGroup.mk g : Γ ⧸ N).out :=
        congrFun h1 (QuotientGroup.mk g)
      rw [hg, ((mem_Zl ρ).1 z.2).2, ((mem_Zl ρ).1 z'.2).2, key, h1']
  have hfin := finZ_local l x.A G0.Γ (pairedDualFirstOrderDualMatrixSpace n x.A (x.Am m) k.g x.a) rep hΦ hLCrep hl
  have key : ∀ z ∈ TwZ k (x.Am m), ∃ y ∈ Zl rep, y G0.c = 0 ∧
      ∀ g : G0.frame.G₀, (y (g : G0.Γ) : Matrix _ _ _) = z g := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine (polZ l G0.frame x.A (DD (x.Am m) k.g) n _ _ _ rep hrep).1 z h1 ?_ h3 h4
    apply finTw_lc
    intro i j
    exact (adicLC G0.frame.G₀ (DD (x.Am m) k.g) _ m _ htR).1 (h2 i j)
  let φ : TwZ k (x.Am m) → Zl rep := fun z => ⟨(key z.1 z.2).choose, (key z.1 z.2).choose_spec.1⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    funext g
    have ha := (key a.1 a.2).choose_spec.2.2 g
    have hb := (key b.1 b.2).choose_spec.2.2 g
    have he : (key a.1 a.2).choose = (key b.1 b.2).choose := congrArg Subtype.val hab
    rw [← ha, ← hb, he]
  exact Set.finite_coe_iff.mp (Finite.of_injective φ hinj)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.Rho1MapReductionLevel
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def ddBaseCompRingHom (X : Type) [CommRing X] (g : ℕ) : DD X g →+* X where
  toFun := DD.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem sandwich_map_smul {R X : Type} [CommRing R] [CommRing X] {n : ℕ} (α : R → X) (φ : R →+ X)
    (c : R) (P Z Q : Matrix (Fin n) (Fin n) R) (h : ∀ i j u, φ (u * Z i j) = α u * φ (Z i j))
    (hα : ∀ u v, α (u * v) = α u * α v) :
    (c • (P * Z * Q)).map φ = α c • (P.map α * Z.map φ * Q.map α) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show c * (P i a * Z a b * Q b j) = (c * (P i a * Q b j)) * Z a b by ring, h, hα, hα]
  ring

private theorem rho1_map_ddBaseCompRingHom_eq_mat {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (k.ρ1 x.A g).map (ddBaseCompRingHom x.A k.g) = mat x.ρ g := by
  have h1 : (1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)).map (ddBaseCompRingHom x.A k.g) = 1 := by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
    exact add_eq_left.2 (Matrix.ext fun _ _ => rfl)
  rw [Kap.ρ1, Matrix.map_mul, h1, one_mul]
  exact Matrix.ext fun _ _ => rfl

private theorem rho1_map_algebraMap_am_eq_rho1 {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (m : ℕ) (g : F.G₀) :
    (k.ρ1 x.A g).map (fun y => (⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j),
      fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩ : DD (x.Am m) k.g)) =
      k.ρ1 (x.Am m) g := by
  change (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = _
  rw [Kap.ρ1, Kap.ρ1, map_mul, map_add (f := _), map_one]
  refine congrArg₂ (· * ·) (congrArg (1 + ·) (Matrix.ext fun i j => ?_)) (Matrix.ext fun i j => ?_)
  · ext <;> simp [DD.epM]
  · exact (x.redD k.g m).commutes _

private theorem site_vector_first {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (D : Subgroup F.G₀)
    (h4 : x.N4 D) (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)) (ha : ∀ i j, (Z i j).a = 0) (he : ∀ i j, (Z i j).ep = 0)
    (hZ : ∀ g ∈ D, epsD k x.A g • (k.ρ1 x.A g * Z * k.ρ1 x.A g⁻¹) = Z) : Z = 0 := by
  have key : ∀ φ : DD x.A k.g →+ x.A, (∀ i j u, φ (u * Z i j) = u.a * φ (Z i j)) → ∀ i j, φ (Z i j) = 0 := by
    intro φ hφ
    have : Z.map φ = 0 := by
      refine h4 _ fun g hg => ?_
      have e := sandwich_map_smul (ddBaseCompRingHom x.A k.g) φ (epsD k x.A g) (k.ρ1 x.A g) Z (k.ρ1 x.A g⁻¹) hφ (map_mul _)
      rw [hZ g hg, rho1_map_ddBaseCompRingHom_eq_mat, rho1_map_ddBaseCompRingHom_eq_mat] at e
      conv_rhs => rw [e]
      rw [smul_mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
      rfl
    exact fun i j => congrFun (congrFun this i) j
  have h' : ∀ t i j, (Z i j).ep' t = 0 := fun t =>
    key ⟨⟨fun y => y.ep' t, rfl⟩, fun _ _ => rfl⟩ fun i j u => by
      show (u * Z i j).ep' t = u.a * (Z i j).ep' t
      simp [ha]
  have h'' : ∀ i j, (Z i j).eta = 0 :=
    key ⟨⟨fun y => y.eta, rfl⟩, fun _ _ => rfl⟩ fun i j u => by
      show (u * Z i j).eta = u.a * (Z i j).eta
      simp [ha, he, h']
  refine Matrix.ext fun i j => ?_
  ext <;> simp [ha, he, h', h'']

theorem UpperTheory.V.Pa.h0v0 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (D : Subgroup F.G₀), x.N4 D → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ ∀ g ∈ D, epsD k (x.Am m) g • (k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹) = Y}.ncard ≤ Nat.card x.K ^ C := by
  intro l _ F n x k D h4
  obtain ⟨C, hC⟩ := UpperTheory.V.Pa.fixBd l F n x k _ false false false true false false true false D
    (fun s => algebraMap ℤ_[l] x.A (F.ε (s : F.G₀) : ℤ_[l])) (fun s => k.ρ1 x.A s) (fun s => k.ρ1 x.A (s : F.G₀)⁻¹)
    false rfl
  refine ⟨C, fun m => ?_⟩
  have h := hC m
  rw [(Submodule.eq_bot_iff (_ ⊓ _ ⊓ _)).2 ?_, finrank_bot, mul_zero, zero_add] at h
  · refine le_of_eq_of_le ?_ h
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq, rho1_map_algebraMap_am_eq_rho1, Subtype.forall, epsD, algebraMap_smul, Bool.false_eq_true, false_imp_iff,
      true_and]
    rfl
  · rintro Z ⟨⟨h1, -⟩, h2⟩
    refine site_vector_first k D h4 Z (fun i j => ?_) (fun i j => ?_) fun g hg => ?_
    · by_cases e : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
      · exact ((h1 i j).1 e).1 rfl
      · exact ((h1 i j).2 e).1 rfl
    · by_cases e : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
      · exact ((h1 i j).1 e).2.1 rfl
      · exact ((h1 i j).2 e).2.1 rfl
    · have e := (Submodule.mem_iInf _).1 h2 ⟨g, hg⟩
      rw [epsD, algebraMap_smul, mul_assoc, ← sub_eq_zero]
      exact e
end

