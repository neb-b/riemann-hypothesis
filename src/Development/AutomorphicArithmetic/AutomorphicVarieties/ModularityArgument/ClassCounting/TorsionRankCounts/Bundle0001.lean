module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.KStability
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.Bridge
section
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

private theorem d_eq (A G : Type) [CommRing A] [Group G] (k : ℕ) (z : Ch A G (k + 1)) :
    (groupHomology.inhomogeneousChains (Rep.trivial A G A)).d (k + 1) k z = bd A G k z := by
  rw [groupHomology.inhomogeneousChains.d_def]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | single g c =>
    rw [groupHomology.inhomogeneousChains.d_single]
    simp [bd, Finsupp.linearCombination_single, Finset.smul_sum, smul_smul, mul_comm c]

private theorem i_inj (A G : Type) [CommRing A] [Group G] (k : ℕ) :
    Function.Injective (groupHomology.iCycles (Rep.trivial A G A) k) :=
  (ModuleCat.mono_iff_injective (groupHomology.iCycles (Rep.trivial A G A) k)).1 inferInstance

private noncomputable def mk (A G : Type) [CommRing A] [Group G] (k : ℕ) :
    LinearMap.ker (bd A G k) →ₗ[A] groupHomology.cycles (Rep.trivial A G A) (k + 1) where
  toFun z := groupHomology.cyclesMk (k + 1) k (by simp) z.1 ((d_eq A G k z.1).trans z.2)
  map_add' a b := i_inj A G _ (by rw [map_add (f := _), groupHomology.iCycles_mk, groupHomology.iCycles_mk, groupHomology.iCycles_mk]; rfl)
  map_smul' c a := i_inj A G _ (by rw [map_smul, groupHomology.iCycles_mk, groupHomology.iCycles_mk]; rfl)

private theorem i_mk (A G : Type) [CommRing A] [Group G] (k : ℕ) (z : LinearMap.ker (bd A G k)) :
    groupHomology.iCycles (Rep.trivial A G A) (k + 1) (mk A G k z) = z.1 := by
  simp only [_root_.mk, LinearMap.coe_mk, AddHom.coe_mk]
  exact groupHomology.iCycles_mk _ _ _

private theorem pi_zero (A G : Type) [CommRing A] [Group G] (k : ℕ) (z : LinearMap.ker (bd A G k)) :
    groupHomology.π (Rep.trivial A G A) (k + 1) (mk A G k z) = 0 ↔ Bd z.1 := by
  let K := groupHomology.inhomogeneousChains (Rep.trivial A G A)
  have hex : (ShortComplex.mk (K.toCycles (k + 2) (k + 1)) (K.homologyπ (k + 1))
      (K.toCycles_comp_homologyπ _ _)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel (k + 2) (k + 1) (by simp))
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hti : ∀ y, groupHomology.iCycles (Rep.trivial A G A) (k + 1) (K.toCycles (k + 2) (k + 1) y) =
      bd A G (k + 1) y := by
    intro y
    rw [← d_eq A G (k + 1) y, ← K.toCycles_i (k + 2) (k + 1)]
    rfl
  constructor
  · intro h
    obtain ⟨y, hy⟩ := hex _ h
    refine ⟨y, ?_⟩
    have := congrArg (groupHomology.iCycles (Rep.trivial A G A) (k + 1)) hy
    rw [i_mk] at this
    simpa [hti] using this
  · rintro ⟨y, hy⟩
    have hm : mk A G k z = K.toCycles (k + 2) (k + 1) y := by
      apply i_inj
      rw [i_mk, hti, hy]
    rw [hm]
    exact congrArg (fun f => f y) (congrArg ModuleCat.Hom.hom (K.toCycles_comp_homologyπ (k + 2) (k + 1)))

theorem UpperTheory.V.ZK.Up.bridge : UpperTheory.V.ZK.Up.Bridge := by
  intro k
  refine ⟨fun G _ => ((groupHomology.π (Rep.trivial ℤ G ℤ) (k + 1)).hom ∘ₗ mk ℤ G k).toAddMonoidHom,
    ?_, ?_, ?_⟩
  · intro G _ x
    refine groupHomology_induction_on x ?_
    intro c
    have hc : groupHomology.iCycles (Rep.trivial ℤ G ℤ) (k + 1) c ∈ LinearMap.ker (bd ℤ G k) := by
      rw [LinearMap.mem_ker, ← d_eq]
      exact congrArg (fun g => g.hom c)
        ((groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)).iCycles_d (k + 1) k)
    refine ⟨⟨_, hc⟩, ?_⟩
    have hm : mk ℤ G k ⟨_, hc⟩ = c := i_inj ℤ G _ (by rw [i_mk])
    simp [hm]
  · intro G _ z
    exact pi_zero ℤ G k z
  · intro G H _ _ f z z' hz
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply, grpHMap]
    rw [groupHomology.π_map_apply]
    congr 1
    apply i_inj
    have h1 := congrArg (fun g => g.hom (mk ℤ G k z))
      (HomologicalComplex.cyclesMap_i (groupHomology.chainsMap f (trivHom f)) (k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [i_mk, hz]
    erw [h1, i_mk]
    induction (z : Ch ℤ G (k + 1)) using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | single g a =>
      rw [groupHomology.chainsMap_f_single]
      simp only [cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.FibCount
section
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

theorem UpperTheory.V.ZK.Up.fibCount : UpperTheory.V.ZK.Up.FibCount := by
  intro Y T B _ _ _ _ β g c hc S hS
  classical
  choose! y hy using hS
  have := Fintype.ofFinite T
  calc S.card ≤ c * (S.image (fun s => β (y s))).card := by
        apply Finset.card_le_mul_card_image
        intro t _
        rcases (S.filter (fun s => β (y s) = t)).eq_empty_or_nonempty with hF | ⟨s₀, hs₀⟩
        · rw [hF]
          simp
        · rw [← Finset.card_image_of_injective _ (sub_left_injective (b := s₀))]
          apply hc
          intro u hu
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hu
          have hs' := Finset.mem_filter.1 hs
          have hs₀' := Finset.mem_filter.1 hs₀
          refine ⟨y s - y s₀, by rw [map_sub, hs'.2, hs₀'.2, sub_self], ?_⟩
          rw [map_sub, ← hy s hs'.1, ← hy s₀ hs₀'.1]
    _ ≤ c * Nat.card T := by
        apply Nat.mul_le_mul_left
        rw [Nat.card_eq_fintype_card]
        exact Finset.card_le_univ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.PhiZSeq
section
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem UpperTheory.V.ZK.Up.phi_zSeq {R B : Type} [CommRing R] [AddCommGroup B] {m l : ℕ} (hl : 0 < l)
    (φ : ∀ n : ℕ, grpH (GL (Fin n) R) m →+ B) (hφ : IsPrimH φ) (n t : ℕ) :
    ∃ c : ℤ, ∀ x : grpH (GL (Fin n) R) m,
      φ (lev l n t) (zSeq R hl x t) = ((l : ℤ) ^ t * (1 - l * c)) • φ n x := by
  induction t with
  | zero => exact ⟨0, fun x => by simp only [pow_zero, mul_zero, sub_zero, mul_one, one_smul]; rfl⟩
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (l : ℤ) ^ t - l * c * (l : ℤ) ^ t, fun x => ?_⟩
    have h : φ (lev l n (t + 1)) (zSeq R hl x (t + 1)) =
        φ (l * lev l n t) ((grpHMap (psi R l (lev l n t)) m).hom (zSeq R hl x t) -
          l ^ (t + 2) • (grpHMap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) m).hom
            (zSeq R hl x t)) := rfl
    rw [h, map_sub, map_nsmul, hφ.psi, hφ.stab, hc, ← natCast_zsmul, ← natCast_zsmul, ← sub_smul, smul_smul]
    congr 1
    push_cast
    ring

theorem UpperTheory.V.ZK.Up.zVal :
    UpperTheory.V.ZK.Up.ZVal := by
  intro R B _ _ m l ν hl hB φ hφ n t
  obtain ⟨c, hc⟩ := UpperTheory.V.ZK.Up.phi_zSeq hl φ hφ n t
  refine ⟨∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i, fun x => ?_⟩
  have hg : (∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i) * ((l : ℤ) ^ t * (1 - l * c)) =
      (l : ℤ) ^ t - ((l : ℤ) ^ t * c ^ ν) * ((l ^ ν : ℕ) : ℤ) := by
    have := geom_sum_mul_neg ((l : ℤ) * c) ν
    push_cast
    rw [mul_left_comm, this, mul_pow]
    ring
  rw [map_zsmul, hc, smul_smul, hg, sub_smul, mul_smul _ ((l ^ ν : ℕ) : ℤ), natCast_zsmul, hB, smul_zero, sub_zero,
    ← natCast_zsmul, Nat.cast_pow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCountAlt
section
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem rankCount_gen (M : Type) [AddCommGroup M] [Module.Finite ℤ M] (r : ℕ)
    (hr : Module.rank ℤ M ≤ r) :
    ∃ (s : ℕ) (v : Fin s → M), s ≤ r ∧ ∀ m : M, ∃ c : Fin s → ℤ,
      m - ∑ i, c i • v i ∈ Submodule.torsion ℤ M := by
  classical
  haveI : Module.Free ℤ (M ⧸ Submodule.torsion ℤ M) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ (M ⧸ Submodule.torsion ℤ M)
  have hs : Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) ≤ r := by
    have h1 : (Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) : Cardinal) ≤ r := by
      rw [Module.finrank_eq_rank]
      exact (rank_quotient_le _).trans hr
    exact_mod_cast h1
  have hv : ∀ i, ∃ v : M, (Submodule.torsion ℤ M).mkQ v = b i :=
    fun i => Submodule.mkQ_surjective _ (b i)
  choose v hv using hv
  refine ⟨_, v, hs, fun m => ⟨fun i => b.repr ((Submodule.torsion ℤ M).mkQ m) i, ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
  simp only [map_smul, hv]
  rw [b.sum_repr, sub_self]

private theorem zsmul_eq_toNat_emod_nsmul_of_nsmul_eq_zero {B : Type} [AddCommGroup B] (q : ℕ) (hq : 0 < q) (w : B)
    (hw : q • w = 0) (a : ℤ) : a • w = ((a % (q : ℤ)).toNat) • w := by
  have h0 : 0 ≤ a % (q : ℤ) := Int.emod_nonneg _ (by omega)
  rw [← natCast_zsmul, Int.toNat_of_nonneg h0]
  have ha : a = a % (q : ℤ) + (a / (q : ℤ)) * (q : ℤ) := by
    rw [Int.emod_def]
    ring
  conv_lhs => rw [ha]
  rw [add_smul, mul_smul, natCast_zsmul, hw, smul_zero, add_zero]

theorem UpperTheory.V.ZK.Up.rankCount :
    UpperTheory.V.ZK.Up.RankCount := by
  intro H B _ _ q r hq hB hT J hJ f S hS
  classical
  haveI := Fintype.ofFinite (AddCommGroup.torsion H)
  choose! x hxJ hx using hS
  let J' : Submodule ℤ H := Submodule.span ℤ ((fun b => x b) '' (S : Set B))
  haveI : Module.Finite ℤ J' := Module.Finite.span_of_finite _ ((S.finite_toSet).image _)
  have hJJ : J' ≤ J := Submodule.span_le.2 (by
    rintro _ ⟨b, hb, rfl⟩
    exact hxJ b hb)
  have hJ' : Module.rank ℤ J' ≤ r := (Submodule.rank_mono hJJ).trans hJ
  obtain ⟨s, v, hsr, hv⟩ := rankCount_gen J' r hJ'
  let Φ : (Fin s → Fin q) × AddCommGroup.torsion H → B :=
    fun p => ∑ i, ((p.1 i : ℕ)) • f ((v i : J') : H) + f p.2
  have hsub : S ⊆ Finset.univ.image Φ := by
    intro b hb
    have hm : x b ∈ J' := Submodule.subset_span ⟨b, hb, rfl⟩
    obtain ⟨c, hc⟩ := hv ⟨x b, hm⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hc
    have ht : (((⟨x b, hm⟩ : J') - ∑ i, c i • v i : J') : H) ∈ AddCommGroup.torsion H := by
      rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨(a : ℤ), nonZeroDivisors.coe_ne_zero a, ?_⟩
      have := congrArg (fun y : J' => (y : H)) ha
      simpa [Submonoid.smul_def] using this
    refine Finset.mem_image.2 ⟨(fun i => ⟨(c i % (q : ℤ)).toNat, ?_⟩, ⟨_, ht⟩), Finset.mem_univ _, ?_⟩
    · have h1 : c i % (q : ℤ) < q := Int.emod_lt_of_pos _ (by omega)
      have h2 : 0 ≤ c i % (q : ℤ) := Int.emod_nonneg _ (by omega)
      omega
    · simp only [Φ]
      have hxb : x b = (((⟨x b, hm⟩ : J') - ∑ i, c i • v i : J') : H) + ∑ i, c i • ((v i : J') : H) := by
        simp
      conv_rhs => rw [hx b hb, hxb]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_toNat_emod_nsmul_of_nsmul_eq_zero q hq _ (hB _)]
  calc S.card ≤ (Finset.univ.image Φ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin s → Fin q) × AddCommGroup.torsion H)).card := Finset.card_image_le
    _ = q ^ s * Nat.card (AddCommGroup.torsion H) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          Nat.card_eq_fintype_card]
    _ ≤ q ^ r * Nat.card (AddCommGroup.torsion H) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq hsr)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RqFacts
section
open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

theorem UpperTheory.V.ZK.Up.rqFacts : UpperTheory.V.ZK.Up.RqFacts := by
  intro q
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G _ m z
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | single g a =>
      ext i
      simp only [bd, rq, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
        Finsupp.linearCombination_single, Finsupp.smul_apply, Finsupp.add_apply,
        Finsupp.finsetSum_apply, Finsupp.mapRange_apply, smul_eq_mul]
      push_cast
      unfold Finsupp.single
      split_ifs <;> simp [Pi.single_apply, apply_ite]
  · intro G H _ _ f m z
    simp only [cm, rq, Finsupp.lmapDomain_apply, Finsupp.mapRange.addMonoidHom_apply]
    exact Finsupp.mapDomain_mapRange _ _ _ _ (fun _ _ => by simp)
  · intro G m y
    refine ⟨Finsupp.mapRange (fun x : ZMod q => (x.cast : ℤ)) (by simp) y, ?_⟩
    ext i
    simp [rq]
  · intro G m z
    constructor
    · intro h
      have hd : ∀ i, (q : ℤ) ∣ z i := by
        intro i
        have := DFunLike.congr_fun h i
        simpa [rq, ZMod.intCast_zmod_eq_zero_iff_dvd] using this
      refine ⟨Finsupp.mapRange (fun x : ℤ => x / q) (by simp) z, ?_⟩
      ext i
      simp [Int.mul_ediv_cancel' (hd i)]
    · rintro ⟨w, rfl⟩
      ext i
      simp [rq]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.TorsStab
section
open CategoryTheory NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem UpperTheory.V.ZK.Up.card_tors_eq {M N : Type} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) :
    Nat.card (AddCommGroup.torsion M) = Nat.card (AddCommGroup.torsion N) := by
  have key : ∀ x : M, x ∈ AddCommGroup.torsion M ↔ e x ∈ AddCommGroup.torsion N := by
    intro x
    rw [AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]
    exact (Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm
  exact Nat.card_congr (e.toEquiv.subtypeEquiv key)

theorem UpperTheory.V.ZK.Up.torsStab :
    UpperTheory.V.ZK.Up.TorsStab := by
  intro L _ _ hL m n n' hn hnn'
  haveI := hL
  have hiso : ∀ k, 2 * m + 4 ≤ k → IsIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m) :=
    fun k hk => PositivityTheory.v8.KStability.kStability (𝓞 L) 2 (dedekindSR (𝓞 L)) m k (by omega)
  have he : Nonempty ((grpH (GL (Fin n) (𝓞 L)) m : Type) ≃+ (grpH (GL (Fin n') (𝓞 L)) m : Type)) := by
    induction n', hnn' using Nat.le_induction with
    | base => exact ⟨AddEquiv.refl _⟩
    | succ k hk ih =>
      obtain ⟨e⟩ := ih
      haveI := hiso k (by omega)
      exact ⟨e.trans (asIso (grpHMap (stab (𝓞 L) k (k + 1) (Nat.le_succ k)) m)).toLinearEquiv.toAddEquiv⟩
  obtain ⟨e⟩ := he
  have key : ∀ x, x ∈ AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type) ↔
      e x ∈ AddCommGroup.torsion (grpH (GL (Fin n') (𝓞 L)) m : Type) := by
    intro x
    rw [AddCommGroup.mem_torsion, AddCommGroup.mem_torsion]
    exact (Function.Injective.isOfFinAddOrder_iff (f := e.toAddMonoidHom) e.injective).symm
  have hfin : Finite (AddCommGroup.torsion (grpH (GL (Fin n) (𝓞 L)) m : Type)) :=
    (UpperTheory.V.KT.tors_le L n m).1
  refine ⟨Finite.of_equiv _ (e.toEquiv.subtypeEquiv key), ?_⟩
  rw [← UpperTheory.V.ZK.Up.card_tors_eq e]
  rfl
end

