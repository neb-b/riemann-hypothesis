module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0007
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0009
public import ReciprocityTheory.GroupCohomology.Bundle0008
public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.ImportsAlt
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0002
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfMemBrKerOfCoprime
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem layer_inflation_h2_injective [(subG p K L).Normal] : Injective ((layerInf p K L).hom.H 2) :=
  multiplicative_inflation_h2_injective p K (subG p K L) (isClosed_subG p K L) _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)

theorem layerInf_layerInfl {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] (n : ℕ) (x : (layer p K L).H n) :
    (layerInf p K L').hom.H n ((layerInfl h).hom.H n x) = (layerInf p K L).hom.H n x := by
  induction x using Cx.H_ind with
  | h x hx => rfl

theorem BrLK_mono {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] : BrLK p K L ≤ BrLK p K L' := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(layerInfl h).hom.H 2 x, layerInf_layerInfl h 2 x⟩

theorem card_BrLK [(subG p K L).Normal] : Nat.card (BrLK p K L) = Nat.card ((layer p K L).H 2) :=
  (Nat.card_congr (LinearEquiv.ofInjective ((layerInf p K L).hom.H 2) layer_inflation_h2_injective).toEquiv).symm

theorem mem_BrKer_iff (h : K ≤ L) (x : Br p K) :
    x ∈ BrKer h ↔ (resP (kbarT p K) (subG p K L)).hom.H 2 x = 0 := by
  obtain ⟨e, he, hf⟩ := exists_resPair_factor h
  show (resPair h).hom.H 2 x = 0 ↔ _
  rw [hf 2 x]
  exact map_eq_zero_iff _ (he 2).1

theorem BrKer_eq_BrLK (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] :
    BrKer h = BrLK p K L := by
  ext x
  rw [mem_BrKer_iff]
  exact infRes2_exact (kbarT p K) (subG p K L) (isOpen_subG hL) _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)
    (restricted_multiplicative_h1_subsingleton p K _) x

theorem degLK_smul_eq_zero (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K) (hx : x ∈ BrKer h) :
    degLK p K L • x = 0 := by
  have := finiteIndex_subG (K := K) hL
  obtain ⟨cor, -, hcor⟩ := cor_holds ℤ (GK p K) (kbarT p K) (subG p K L) (isOpen_subG hL)
  have h2 := hcor 2 x
  rw [(mem_BrKer_iff h x).1 hx, map_zero] at h2
  exact h2.symm

theorem eq_zero_of_mem_BrKer_of_coprime (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K)
    (hx : x ∈ BrKer h) (k : ℕ) (hk : k • x = 0) (hc : Nat.Coprime k (degLK p K L)) : x = 0 := by
  have h1 := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hk)
    (addOrderOf_dvd_of_nsmul_eq_zero (degLK_smul_eq_zero hL h x hx))
  rw [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one] at h1
  exact AddMonoid.addOrderOf_eq_one_iff.1 h1

theorem exists_mem_BrKer (hK : FiniteDimensional ℚ_[p] K) (x : Br p K) :
    ∃ (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ L), FiniteDimensional ℚ_[p] L ∧
      (subG p K L).Normal ∧ x ∈ BrKer h := by
  obtain ⟨N, hN, hNo, hx⟩ := FiniteLevelCohomology.exists_level (kbarT p K) 2 x
  obtain ⟨L, h, hL, rfl⟩ := exists_subG_eq_of_isOpen hK N hNo
  refine ⟨L, h, hL, hN, ?_⟩
  rw [BrKer_eq_BrLK hL h]
  exact hx _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.HSubsingletonOfUniquelyDivisible
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem h_subsingleton_of_uniquely_divisible [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {R : Type} [CommRing R]
    (M : TRep R G) [DiscreteTopology M.V] (hM : ∀ k : ℕ, 0 < k → Bijective fun m : M.V => k • m)
    (n : ℕ) (hn : 0 < n) : Subsingleton (M.H n) := by
  suffices h : ∀ x : M.H n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨-, h⟩ := finiteLevel_holds R G M n x
  obtain ⟨k, hk, hkx⟩ := h hn
  let e : M.V ≃ₗ[R] M.V := LinearEquiv.ofBijective ((k : R) • LinearMap.id) (by
    have := hM k hk
    convert this using 2 with m
    simp [Nat.cast_smul_eq_nsmul])
  have he : ∀ m, e m = (k : R) • m := fun m => rfl
  let Q : Pair M M := Pair.ofMap e.symm.toLinearMap continuous_of_discreteTopology (by
    intro g m
    apply e.injective
    show e (e.symm _) = e (M.rho g (e.symm m))
    rw [e.apply_symm_apply, he, ← map_smul, ← he, e.apply_symm_apply])
  have hQ : ∀ y : M.H n, (k : R) • Q.hom.H n y = y := by
    intro y
    induction y using Cx.H_ind with
    | h c hc =>
      rw [Cx.Hom.H_cls, Cx.cls_smul]
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      exact e.apply_symm_apply _
  rw [← hQ x, ← map_smul, Nat.cast_smul_eq_nsmul, hkx, map_zero]

theorem h_subsingleton_of_divisible [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : TRep ℤ G) [DiscreteTopology M.V] (hM : ∀ k : ℕ, 0 < k → Bijective fun m : M.V => k • m)
    (n : ℕ) (hn : 0 < n) : Subsingleton (M.H n) :=
  h_subsingleton_of_uniquely_divisible G M hM n hn

theorem h_rat_subsingleton [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((trivRep G ℚ).H n) := by
  refine h_subsingleton_of_divisible G (trivRep G ℚ) (fun k hk => ?_) n hn
  show Bijective fun m : ℚ => k • m
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun a b h => ?_, fun y => ⟨y / k, ?_⟩⟩
  · simpa [nsmul_eq_mul, hk'] using h
  · simp only [nsmul_eq_mul]; field_simp

theorem admissible_int_rat_sequence : admitted (trivMap G (Int.castAddHom ℚ)) (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · have hi : Injective (trivMap G (Int.castAddHom ℚ)).u := Int.cast_injective (α := ℚ)
    exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology hi
      fun _ _ => isOpen_discrete _).isEmbedding
  · intro (y : ℚ)
    show (QuotientAddGroup.mk y : QZ) = 0 ↔ y ∈ Set.range (Int.castAddHom ℚ)
    rw [QuotientAddGroup.eq_zero_iff]; rfl
  · exact ⟨Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range),
      continuous_of_discreteTopology, Function.surjInv_eq _⟩

theorem conn_int_rat_bijective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (δ : ∀ n, (trivRep G QZ).H n →ₗ[ℤ] (trivRep G ℤ).H (n + 1))
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ) (n : ℕ) (hn : 0 < n) :
    Bijective (δ n) := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ', h1, h2⟩, hu⟩ := lES_holds ℤ _ _ _ _ _ hs
  obtain rfl := hu δ δ' hδ h1
  have s1 := h_rat_subsingleton G n hn
  have s2 := h_rat_subsingleton G (n + 1) n.succ_pos
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (h2.exC n x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact (h2.exA n y).1 (Subsingleton.elim _ _)

def oneCocycleEquivCharacters : Gal.Z1 (trivRep G QZ).rho ≃+ charGrp G where
  toFun c := ⟨AddMonoidHom.mk' (fun a : Additive G => (c.1 a.toMul : QZ)) fun a b => c.2.2 a.toMul b.toMul,
    (@IsLocallyConstant.iff_continuous G (trivRep G QZ).V _ _ _ c.1).2 c.2.1⟩
  invFun χ := ⟨fun g => χ.1 (Additive.ofMul g),
    (@IsLocallyConstant.iff_continuous G (trivRep G QZ).V _ _ _ _).1 χ.2,
    fun g h => map_add χ.1 (Additive.ofMul g) (Additive.ofMul h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem one_coboundaries_trivial_eq_bot (A : Type) [AddCommGroup A] : Gal.B1 (trivRep G A).rho = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨m, rfl⟩
  refine (Submodule.mem_bot _).2 (funext fun g => ?_)
  exact sub_self m

theorem exists_h1_equiv_characters : ∃ e : (trivRep G QZ).H 1 ≃+ charGrp G,
    ∀ x hx g, (e ((trivRep G QZ).coch.cls 1 x hx)).1 (Additive.ofMul g) = x.1 ![g] := by
  obtain ⟨-, -, ⟨e, he⟩, -⟩ := low_holds ℤ G (trivRep G QZ)
  have hB : (Gal.B1 (trivRep G QZ).rho).comap (Gal.Z1 (trivRep G QZ).rho).subtype = ⊥ := by
    rw [one_coboundaries_trivial_eq_bot, Submodule.comap_bot, Submodule.ker_subtype]
  refine ⟨e.toAddEquiv.trans ((Submodule.quotEquivOfEqBot _ hB).toAddEquiv.trans (oneCocycleEquivCharacters G)), ?_⟩
  intro x hx g
  obtain ⟨hz, h⟩ := he x hx
  show (oneCocycleEquivCharacters G (Submodule.quotEquivOfEqBot _ hB (e _))).1 (Additive.ofMul g) = _
  rw [h, Submodule.quotEquivOfEqBot_apply_mk]
  rfl

theorem exists_h2_int_equiv_characters [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ∃ e : (trivRep G ℤ).H 2 ≃+ charGrp G, ∀ δ, Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ x hx g, (e (δ 1 ((trivRep G QZ).coch.cls 1 x hx))).1 (Additive.ofMul g) = x.1 ![g] := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ', h1, -⟩, hu⟩ := lES_holds ℤ _ _ _ _ _ hs
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  let d : (trivRep G QZ).H 1 ≃+ (trivRep G ℤ).H 2 :=
    AddEquiv.ofBijective (δ' 1).toAddMonoidHom (conn_int_rat_bijective G δ' h1 1 one_pos)
  refine ⟨d.symm.trans e, fun δ hδ x hx g => ?_⟩
  obtain rfl := hu δ δ' hδ h1
  show (e (d.symm (d _))).1 _ = _
  rw [d.symm_apply_apply, he]

theorem charGrp_eval_injective (s : G) (hs : Dense (Subgroup.zpowers s : Set G)) :
    Injective fun χ : charGrp G => χ.1 (Additive.ofMul s) := by
  have key : ∀ ψ : charGrp G, ψ.1 (Additive.ofMul s) = 0 → ψ = 0 := by
    intro ψ h
    have hcl : IsClosed {g : G | ψ.1 (Additive.ofMul g) = 0} := (IsLocallyConstant.isClopen_fiber ψ.2 0).1
    have hsub : (Subgroup.zpowers s : Set G) ⊆ {g : G | ψ.1 (Additive.ofMul g) = 0} := by
      rintro _ ⟨k, rfl⟩
      show ψ.1 (Additive.ofMul (s ^ k)) = 0
      rw [ofMul_zpow, map_zsmul, h, smul_zero]
    have hall := closure_minimal hsub hcl
    rw [hs.closure_eq] at hall
    exact Subtype.ext (AddMonoidHom.ext fun a => hall (Set.mem_univ a.toMul))
  intro χ χ' h
  refine sub_eq_zero.1 (key (χ - χ') ?_)
  show χ.1 (Additive.ofMul s) - χ'.1 (Additive.ofMul s) = 0
  exact sub_eq_zero.2 h

theorem charGrp_eval_bijective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (s : G)
    (hs : IsZHat G s) : Bijective fun χ : charGrp G => χ.1 (Additive.ofMul s) := by
  refine ⟨charGrp_eval_injective G s hs.1, fun (q : (trivRep G QZ).V) => ?_⟩
  obtain ⟨⟨e, he⟩, -⟩ := zHat_holds ℤ G s hs (trivRep G QZ) RationalModIntegerChains.qz_torsion
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk q))
  have h := he c
  rw [hc, e.apply_symm_apply] at h
  obtain ⟨m, hm⟩ := (Submodule.Quotient.eq _).1 h
  have hm' : 0 = q - c.1 s := by rw [← hm]; exact (sub_self m).symm
  exact ⟨oneCocycleEquivCharacters G c, (sub_eq_zero.1 hm'.symm).symm⟩

theorem exists_h2_int_equiv_rat_mod_int [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (s : G)
    (hs : IsZHat G s) : ∃ e : (trivRep G ℤ).H 2 ≃+ QZ, ∀ δ, Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ x hx, e (δ 1 ((trivRep G QZ).coch.cls 1 x hx)) = x.1 ![s] := by
  obtain ⟨e, he⟩ := exists_h2_int_equiv_characters G
  let ev : charGrp G →+ QZ :=
    { toFun := fun χ => χ.1 (Additive.ofMul s), map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact ⟨e.trans (AddEquiv.ofBijective ev (charGrp_eval_bijective G s hs)),
    fun δ hδ x hx => he δ hδ x hx s⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

def OK : Subring K := (Obar p).toSubring.comap (algebraMap K (PadicAlgCl p))

theorem mem_OK_iff (x : K) : x ∈ OK p K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := mem_Obar_iff

theorem norm_algebraMap_padicInt (x : ℤ_[p]) : ‖((algebraMap ℤ_[p] K x : K) : PadicAlgCl p)‖ ≤ 1 := by
  show ‖algebraMap ℚ_[p] (PadicAlgCl p) (x : ℚ_[p])‖ ≤ 1
  exact (PadicAlgCl.norm_extends p (x : ℚ_[p])).le.trans x.2

def zpToOK : ℤ_[p] →+* OK p K :=
  (algebraMap ℤ_[p] K).codRestrict _ fun x => (mem_OK_iff p K _).2 (norm_algebraMap_padicInt p K x)

@[instance_reducible]
def zpAlgOK : Algebra ℤ_[p] (OK p K) := (zpToOK p K).toAlgebra

attribute [local instance] zpAlgOK

theorem isScalarTower_zp_OK : IsScalarTower ℤ_[p] (OK p K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isScalarTower_zp_K_alg : IsScalarTower ℤ_[p] K (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isTorsionFree_zp_K : Module.IsTorsionFree ℤ_[p] K := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  rw [Algebra.smul_def, mul_eq_zero] at h
  refine h.imp (fun h => ?_) id
  have h2 : algebraMap ℚ_[p] K (r : ℚ_[p]) = 0 := h
  rw [map_eq_zero] at h2
  exact PadicInt.ext (by simpa using h2)

theorem isIntegral_zp_K_iff (x : K) :
    IsIntegral ℤ_[p] x ↔ IsIntegral (PadicInt.subring p) (x : PadicAlgCl p) := by
  have := isScalarTower_zp_K_alg p K
  rw [← isIntegral_algebraMap_iff (A := K) (B := PadicAlgCl p) ]
  exact Iff.rfl

theorem isIntegralClosure_OK : IsIntegralClosure (OK p K) ℤ_[p] K := by
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  rw [isIntegral_zp_K_iff, ← norm_le_one_iff_isIntegral, ← mem_OK_iff]
  exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

theorem card_OK_quot_p (hK : FiniteDimensional ℚ_[p] K) :
    Nat.card (OK p K ⧸ Ideal.span {(p : OK p K)}) = p ^ Module.finrank ℚ_[p] K := by
  have := isScalarTower_zp_OK p K
  have := isIntegralClosure_OK p K
  have := isTorsionFree_zp_K p K
  have : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  have : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  have hr := IsIntegralClosure.rank ℤ_[p] ℚ_[p] K (OK p K)
  have hn' : (p : OK p K) = algebraMap ℤ_[p] (OK p K) (p : ℕ) := (map_natCast _ _).symm
  rw [hn', card_quot_span_algebraMap (Module.finBasis ℤ_[p] (OK p K)),
    card_quot_natCast_padicInt p (Fact.out : p.Prime).ne_zero, Fintype.card_fin, hr,
    Nat.padicValNat_def, Nat.Prime.multiplicity_self, pow_one]

theorem isDedekindDomain_OK (hK : FiniteDimensional ℚ_[p] K) : IsDedekindDomain (OK p K) := by
  have := isScalarTower_zp_OK p K
  have := isIntegralClosure_OK p K
  exact IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] K (OK p K)

theorem mem_span_singleton_OK (a b : OK p K) :
    a ∈ Ideal.span {b} ↔ ‖((a : K) : PadicAlgCl p)‖ ≤ ‖((b : K) : PadicAlgCl p)‖ := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    have hc : ‖((c : K) : PadicAlgCl p)‖ ≤ 1 := (mem_OK_iff p K _).1 c.2
    show ‖((c : K) : PadicAlgCl p) * ((b : K) : PadicAlgCl p)‖ ≤ _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  · intro h
    by_cases hb : ((b : K) : PadicAlgCl p) = 0
    · rw [hb, norm_zero] at h
      have ha : ((a : K) : PadicAlgCl p) = 0 := norm_le_zero_iff.1 h
      exact ⟨0, Subtype.ext (Subtype.ext (by rw [ha]; simp))⟩
    · have hb' : 0 < ‖((b : K) : PadicAlgCl p)‖ := norm_pos_iff.2 hb
      refine ⟨⟨(a : K) / (b : K), ?_⟩, Subtype.ext (Subtype.ext ?_)⟩
      · rw [mem_OK_iff]
        show ‖((a : K) : PadicAlgCl p) / ((b : K) : PadicAlgCl p)‖ ≤ 1
        rw [norm_div, div_le_one hb']
        exact h
      · show ((a : K) : PadicAlgCl p) / ((b : K) : PadicAlgCl p) * ((b : K) : PadicAlgCl p) = _
        rw [div_mul_cancel₀ _ hb]

theorem span_singleton_OK_eq {a b : OK p K} (h : ‖((a : K) : PadicAlgCl p)‖ = ‖((b : K) : PadicAlgCl p)‖) :
    Ideal.span {a} = Ideal.span {b} :=
  le_antisymm ((Ideal.span_singleton_le_iff_mem _).2 ((mem_span_singleton_OK p K a b).2 h.le))
    ((Ideal.span_singleton_le_iff_mem _).2 ((mem_span_singleton_OK p K b a).2 h.ge))

def toObar : OK p K →+* Obar p :=
  ((algebraMap K (PadicAlgCl p)).comp (OK p K).subtype).codRestrict (Obar p) fun x => x.2

def resMap : OK p K →+* kbar p := (IsLocalRing.residue (Obar p)).comp (toObar p K)

theorem mem_ker_resMap (x : OK p K) : x ∈ RingHom.ker (resMap p K) ↔ ‖((x : K) : PadicAlgCl p)‖ < 1 := by
  rw [RingHom.mem_ker]
  show IsLocalRing.residue (Obar p) (toObar p K x) = 0 ↔ _
  rw [← map_zero (IsLocalRing.residue (Obar p)), residue_eq_iff]
  show ‖((x : K) : PadicAlgCl p) - 0‖ < 1 ↔ _
  rw [sub_zero]

theorem card_OK_quot_ker : Nat.card (OK p K ⧸ RingHom.ker (resMap p K)) = qK p K := by
  rw [Nat.card_congr (RingHom.quotientKerEquivRange (resMap p K)).toEquiv, qK]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [mem_resK_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨toObar p K x, (x : K).2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨⟨x, hx⟩, x.2⟩, rfl⟩

theorem ker_resMap_eq_span (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1)
    (hπ1 : (π : K) ∈ OK p K) : RingHom.ker (resMap p K) = Ideal.span {(⟨π, hπ1⟩ : OK p K)} := by
  ext x
  rw [mem_ker_resMap, mem_span_singleton_OK]
  by_cases hx : (x : K) = 0
  · rw [hx]; simp
  · have h1 := norm_lt_one_iff_vK p K hK (Units.mk0 (x : K) hx)
    have h2 := norm_le_norm_iff_vK p K hK (Units.mk0 (x : K) hx) π
    rw [hπ] at h2
    exact h1.trans h2.symm

theorem qK_pow_eK (hK : FiniteDimensional ℚ_[p] K) : qK p K ^ eK p K = p ^ Module.finrank ℚ_[p] K := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  have hπ1 : (π : K) ∈ OK p K := (mem_OK_iff p K _).2 ((norm_le_one_iff_vK p K hK π).2 (by omega))
  have := isDedekindDomain_OK p K hK
  have hP := ker_resMap_eq_span p K hK hπ hπ1
  have hprime : (RingHom.ker (resMap p K)).IsPrime := RingHom.ker_isPrime _
  have hbot : RingHom.ker (resMap p K) ≠ ⊥ := by
    rw [hP, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => π.ne_zero (congrArg Subtype.val h)
  have h1 := cardQuot_pow_of_prime (P := RingHom.ker (resMap p K)) hbot (i := eK p K)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, card_OK_quot_ker] at h1
  rw [← h1, ← card_OK_quot_p p K hK, hP, Ideal.span_singleton_pow]
  congr 2
  apply span_singleton_OK_eq
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h2 : vK p K (Units.mk0 (p : K) hp0) = eK p K := vK_p p K _ (by simp)
  have h3 : vK p K (π ^ eK p K) = eK p K := by rw [vK_pow, hπ, mul_one]
  have h4 := (norm_le_norm_iff_vK p K hK (π ^ eK p K) (Units.mk0 (p : K) hp0)).2 (by omega)
  have h5 := (norm_le_norm_iff_vK p K hK (Units.mk0 (p : K) hp0) (π ^ eK p K)).2 (by omega)
  exact le_antisymm (by simpa using h4) (by simpa using h5)

theorem qK_eq_pow_fK (hK : FiniteDimensional ℚ_[p] K) : qK p K = p ^ fK p K := by
  obtain ⟨f, -, hf⟩ := qK_eq_pow p K hK
  rw [fK, hf, Nat.log_pow (Fact.out : p.Prime).one_lt]

theorem fK_pos (hK : FiniteDimensional ℚ_[p] K) : 0 < fK p K := by
  obtain ⟨f, hf0, hf⟩ := qK_eq_pow p K hK
  rwa [fK, hf, Nat.log_pow (Fact.out : p.Prime).one_lt]

theorem eK_mul_fK (hK : FiniteDimensional ℚ_[p] K) : eK p K * fK p K = Module.finrank ℚ_[p] K := by
  have h := qK_pow_eK p K hK
  rw [qK_eq_pow_fK p K hK, ← pow_mul] at h
  rw [mul_comm]
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

