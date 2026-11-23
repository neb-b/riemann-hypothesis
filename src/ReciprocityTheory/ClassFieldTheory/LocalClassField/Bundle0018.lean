module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0017
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0013
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0011
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0010
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0016
public import ReciprocityTheory.GroupCohomology.Bundle0008
public import ReciprocityTheory.GroupCohomology.Bundle0004
public import ReciprocityTheory.GroupCohomology.Bundle0007
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0012
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclicA
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

theorem qz_mem_zmultiples {n : ℕ} (hn : 0 < n) (x : QZ) (hx : n • x = 0) :
    x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have h1 : (QuotientAddGroup.mk (n • q) : QZ) = 0 := hx
  obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h1
  have hk' : (k : ℚ) = n • q := hk
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨k, ?_⟩
  show (QuotientAddGroup.mk (k • ((1 : ℚ) / n)) : QZ) = _
  congr 1
  rw [zsmul_eq_mul, hk', nsmul_eq_mul]
  field_simp

section general

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G)

theorem exists_defect {t : G → ℚ} (χ : Additive G →+ QZ)
    (h : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ (Additive.ofMul g)) :
    ∃ m : (Fin 2 → G) → ℤ, ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
  have : ∀ g : Fin 2 → G, ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := fun g => by
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, h, h, h, ofMul_mul, map_add (f := _), sub_self]
    obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h0
    exact ⟨k, hk⟩
  choose m hm using this
  exact ⟨m, hm⟩

theorem isLocallyConstant_defect {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) : IsLocallyConstant m := by
  refine IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) ?_ Int.cast_injective
  have : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
  rw [this]
  exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
    (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))

theorem defect_cocycle {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (x y w : G) :
    m ![y, w] - m ![x * y, w] + m ![x, y * w] = m ![x, y] := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, hm, hm, hm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
  ring

theorem exists_defect_cocycle {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (a : M.V) (ha : ∀ g, M.rho g a = a) :
    ∃ z : M.coch.X 2, M.coch.d 2 z = 0 ∧ ∀ g, z.1 g = m g • a := by
  have hc : Continuous fun g => m g • a :=
    ((isLocallyConstant_defect ht hm).comp (fun k : ℤ => k • a)).continuous
  refine ⟨⟨fun g => m g • a, hc⟩, Subtype.ext (funext fun v => ?_), fun _ => rfl⟩
  show ReciprocityTheory.Gal.dn M.rho 2 (fun g => m g • a) v = 0
  rw [LowDeg.dn_two_apply, map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul,
    defect_cocycle hm, sub_self, zero_smul]

variable [Fintype G]

theorem sum_defect_smul {m : (Fin 2 → G) → ℤ} (a : M.V) (b : M.coch.X 1)
    (hb : ∀ g, (M.coch.d 1 b).1 g = m g • a) (τ : G) :
    (∑ σ, m ![σ, τ]) • a = ∑ σ, M.rho σ (b.1 ![τ]) := by
  have h1 : ∀ σ : G, m ![σ, τ] • a = M.rho σ (b.1 ![τ]) - b.1 ![σ * τ] + b.1 ![σ] := fun σ => by
    rw [← hb]
    exact LowDeg.dn_one_apply M.rho b.1 ![σ, τ]
  have h2 : ∑ σ, b.1 ![σ * τ] = ∑ σ, b.1 ![σ] := Equiv.sum_comp (Equiv.mulRight τ) (fun σ => b.1 ![σ])
  rw [Finset.sum_smul, Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_add_distrib, Finset.sum_sub_distrib, h2]
  abel

theorem sum_defect {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (τ : G) :
    ((∑ σ, m ![σ, τ] : ℤ) : ℚ) = Fintype.card G * t τ := by
  push_cast
  rw [Finset.sum_congr rfl fun σ _ => hm ![σ, τ]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2 : ∑ σ, t (σ * τ) = ∑ σ, t σ := Equiv.sum_comp (Equiv.mulRight τ) t
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h2]
  simp

theorem exists_cobound_of_norm [DiscreteTopology G] {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (y : M.V) :
    ∃ b : M.coch.X 1, ∀ g, (M.coch.d 1 b).1 g = m g • ∑ ρ, M.rho ρ y := by
  refine ⟨⟨fun w => ∑ ρ, m ![w 0, ρ] • M.rho (w 0 * ρ) y, continuous_of_discreteTopology⟩, fun v => ?_⟩
  show ReciprocityTheory.Gal.dn M.rho 1 (fun w => ∑ ρ, m ![w 0, ρ] • M.rho (w 0 * ρ) y) v = _
  rw [LowDeg.dn_one_apply]
  simp only [Matrix.cons_val_zero]
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Equiv.sum_comp (Equiv.mulLeft (v 1)) (fun ρ => m ![v 0, ρ] • M.rho (v 0 * ρ) y),
    ← Equiv.sum_comp (Equiv.mulLeft (v 0 * v 1)) (fun ρ => M.rho ρ y), map_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [map_zsmul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← sub_smul, ← add_smul, defect_cocycle hm, ← hv]

end general

end ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.RecFunctA
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

section general

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def smulBil (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] : V →ₗ[R] R →ₗ[R] V :=
  (LinearMap.lsmul R V).flip

noncomputable def smulPairing (M : TRep ℤ G) [DiscreteTopology M.V] : Pairing M (trivRep G ℤ) M where
  β := @smulBil ℤ M.V _ _ M.mod
  cont := continuous_of_discreteTopology
  equiv g m n := (@LinearMap.map_smul ℤ M.V M.V _ _ _ M.mod M.mod (M.rho g) (show ℤ from n) m).symm

theorem smulPairing_apply (M : TRep ℤ G) [DiscreteTopology M.V] (x : M.V) (n : ℤ) :
    (smulPairing M).β x n = n • x := int_smul_eq_zsmul M.mod n x

theorem exists_int_cocycle (t : G → ℚ) (m : (Fin 2 → G) → ℤ) (ht : IsLocallyConstant t)
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (y : (trivRep G ℤ).coch.X 2), (trivRep G ℤ).coch.d 2 y = 0 ∧ ∀ g, y.1 g = m g := by
  obtain ⟨z, hz, hzm⟩ := exists_defect_cocycle (trivRep G ℤ) (a := (1 : ℤ)) (fun _ => rfl) ht hm
  exact ⟨z, hz, fun g => (hzm g).trans (mul_one (m g))⟩

theorem cupFun_zero_two {M N P : TRep ℤ G} (b : Pairing M N P) (f : (Fin 0 → G) → M.V) (f' : (Fin 2 → G) → N.V)
    (g : Fin (0 + 2) → G) : cupFun b 0 2 f f' g = b.β (f ![]) (f' g) := by
  unfold cupFun
  rw [show (fun i : Fin 0 => g (Fin.castAdd 2 i)) = ![] from Subsingleton.elim _ _,
    show (fun j : Fin 2 => g (Fin.natAdd 0 j)) = g from funext fun j => congrArg g (Fin.ext (by simp))]
  simp

theorem trep_dn_zero {R : Type} [CommRing R] (M : TRep R G) (f : (Fin 0 → G) → M.V) (v : Fin 1 → G) :
    ReciprocityTheory.Gal.dn M.rho 0 f v = M.rho (v 0) (f ![]) - f ![] :=
  LowDeg.dn_zero_apply M.rho f v

theorem cor_smul_cocycle (M : TRep ℤ G) [DiscreteTopology M.V] (U : Subgroup G) [U.FiniteIndex]
    (hU : IsOpen (U : Set G)) (cor : Cx.Hom (M.resSub U).coch M.coch) (hcor : IsCor M U cor)
    (x : M.V) (hx : ∀ g ∈ U, M.rho g x = x) (x' : M.V) (hx' : corFun M U 0 (fun _ => x) ![] = x')
    (y : (trivRep G ℤ).coch.X 2) (hy : (trivRep G ℤ).coch.d 2 y = 0)
    (zU : (M.resSub U).coch.X 2) (hzU : (M.resSub U).coch.d 2 zU = 0)
    (hzU1 : ∀ g, zU.1 g = (show ℤ from y.1 fun i => (g i : G)) • x)
    (z : M.coch.X 2) (hz : M.coch.d 2 z = 0) (hz1 : ∀ g, z.1 g = (show ℤ from y.1 g) • x') :
    cor.H 2 ((M.resSub U).coch.cls 2 zU hzU) = M.coch.cls 2 z hz := by
  let bP := smulPairing M
  let bU : Pairing (M.resSub U) ((trivRep G ℤ).resSub U) (M.resSub U) :=
    ⟨bP.β, bP.cont, fun g m n => bP.equiv g.1 m n⟩
  let x0 : (M.resSub U).coch.X 0 := ⟨fun _ => x, continuous_const⟩
  have hx0 : (M.resSub U).coch.d 0 x0 = 0 := by
    refine Subtype.ext (funext fun g => ?_)
    refine (trep_dn_zero (M.resSub U) x0.1 g).trans ?_
    show M.rho (g 0).1 x - x = 0
    rw [hx _ (g 0).2, sub_self]
  have hry : ((trivRep G ℤ).resSub U).coch.d 2
      ((Pair.res (trivRep G ℤ) U.subtype continuous_subtype_val).hom.f 2 y) = 0 := Cx.Hom.d_f_eq_zero _ hy
  have hcx : M.coch.d 0 (cor.f 0 x0) = 0 := Cx.Hom.d_f_eq_zero _ hx0
  have key : cor.H (0 + 2) (cupCoh bU 0 2 ((M.resSub U).coch.cls 0 x0 hx0)
      (((trivRep G ℤ).resSub U).coch.cls 2 _ hry)) =
      cupCoh bP 0 2 (M.coch.cls 0 (cor.f 0 x0) hcx) ((trivRep G ℤ).coch.cls 2 y hy) :=
    cupCor_holds ℤ G M (trivRep G ℤ) M U bP bU (cupCoh bP) (cupCoh bU) cor cor hU rfl (cupCoh_isCup bP)
      (cupCoh_isCup bU) hcor hcor 0 2 ((M.resSub U).coch.cls 0 x0 hx0) ((trivRep G ℤ).coch.cls 2 y hy)
  obtain ⟨zU', hzU', hzU1', hzU2'⟩ := cupCoh_isCup bU 0 2 x0 _ hx0 hry
  obtain ⟨w, hw, hw1, hw2⟩ := cupCoh_isCup bP 0 2 (cor.f 0 x0) y hcx hy
  rw [hzU2', hw2] at key
  have e1 : zU' = zU := by
    refine Subtype.ext (funext fun g => ?_)
    rw [hzU1', cupFun_zero_two]
    exact (smulPairing_apply M x _).trans (hzU1 g).symm
  have e2 : w = z := by
    refine Subtype.ext (funext fun g => ?_)
    rw [hw1, cupFun_zero_two, hcor, hx']
    exact (smulPairing_apply M x' _).trans (hz1 g).symm
  subst e1 e2
  exact key

end general

theorem corFun_zero_eq_normHom (hL : FiniteDimensional ℚ_[p] L) (y : KbarMult p) (hy : y ∈ multOf p L)
    (f : (Fin 0 → subG p K L) → (kbarT p K).V) (hf : ∀ g, f g = y) (g : Fin 0 → GK p K) :
    corFun (kbarT p K) (subG p K L) 0 f g = normHom p K L y := by
  have := finite_GalLK (p := p) (K := K) hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  rw [normHom_apply, ← finsum_eq_sum_of_fintype,
    ← finsum_comp_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel (subG p K L))]
  unfold corFun
  simp only [hf]
  refine finsum_congr fun c => ?_
  have h1 : QuotientGroup.quotientRightRelEquivQuotientLeftRel (subG p K L) c =
      (QuotientGroup.mk (c.out⁻¹) : GK p K ⧸ subG p K L) := by
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [h1, kbarRep_out y hy]
  rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.RecUnr
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_ur_lift (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    ∃ t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ, IsLocallyConstant t ∧
      ∀ g : GK p K, (QuotientAddGroup.mk (t (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g) := by
  let sec : QZ → ℚ := Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  have hsec : ∀ q : QZ, (QuotientAddGroup.mk (sec q) : QZ) = q :=
    Function.surjInv_eq (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  let f : GK p K → QZ := fun g => χ.1 (Additive.ofMul g)
  have hf : IsLocallyConstant f := χ.2
  have hfq : ∀ g : GK p K, f (QuotientGroup.mk g : GalLK p K (MaximalUnramifiedExtension p K)).out = f g := by
    intro g
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul (subG p K (MaximalUnramifiedExtension p K)) g
    rw [hn]
    show χ.1 (Additive.ofMul g + Additive.ofMul n.1) = _
    rw [map_add (f := _), hχ n.1 n.2, add_zero]
  have hloc : IsLocallyConstant fun q : GalLK p K (MaximalUnramifiedExtension p K) => f q.out := by
    intro s
    rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isOpen_preimage]
    have h0 : (QuotientGroup.mk : GK p K → GalLK p K (MaximalUnramifiedExtension p K)) ⁻¹'
        ((fun q : GalLK p K (MaximalUnramifiedExtension p K) => f q.out) ⁻¹' s) = f ⁻¹' s := by
      ext g
      show f (QuotientGroup.mk g : GalLK p K (MaximalUnramifiedExtension p K)).out ∈ s ↔ f g ∈ s
      rw [hfq]
    rw [h0]
    exact hf s
  refine ⟨fun q => sec (f q.out), hloc.comp sec, fun g => ?_⟩
  rw [hsec]
  exact hfq g


variable (p K) in
noncomputable def urOfK (a : Kˣ) : (urT p K).V :=
  toLayer p ⟨ofK p K (Additive.ofMul a), le_Kur (K := K) (ofK_mem p K _)⟩

theorem exists_ur_cocycle (a : Kˣ) (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    ∃ (t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ) (z : (urT p K).coch.X 2)
      (hz : (urT p K).coch.d 2 z = 0), IsLocallyConstant t ∧
      (∀ g : GK p K, (QuotientAddGroup.mk (t (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g)) ∧
      (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ (∀ g, z.1 g = m g • urOfK p K a) ∧
      pairBr p K a χ = (layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz) := by
  obtain ⟨t, ht, htχ⟩ := exists_ur_lift χ hχ
  have hex : ∀ g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K), ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
    intro g
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (g 0)
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (g 1)
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [← hσ, ← hτ, ← QuotientGroup.mk_mul, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, htχ, htχ, htχ,
        ofMul_mul, map_add, sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).1 h0
  choose m hm using hex
  have hmc : IsLocallyConstant m := by
    apply IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) _ Int.cast_injective
    have h0 : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
    rw [h0]
    exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  have hzc : Continuous fun g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K) => m g • urOfK p K a :=
    (hmc.comp fun k : ℤ => k • urOfK p K a).continuous
  let z : (urT p K).coch.X 2 := ⟨fun g => m g • urOfK p K a, hzc⟩
  have hinv := (layer_invariant_iff (urOfK p K a)).2 (ofK_mem p K _)
  have hz : (urT p K).coch.d 2 z = 0 := by
    apply LowDeg.coch_d_eq_zero
    funext g
    have h1 : m ![g 1, g 2] - m ![g 0 * g 1, g 2] + m ![g 0, g 1 * g 2] - m ![g 0, g 1] = 0 := by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hm, hm, hm, hm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
      ring
    rw [LowDeg.dn_two_apply]
    show (urT p K).rho (g 0) (m ![g 1, g 2] • urOfK p K a) - m ![g 0 * g 1, g 2] • urOfK p K a +
      m ![g 0, g 1 * g 2] • urOfK p K a - m ![g 0, g 1] • urOfK p K a = 0
    rw [map_zsmul, hinv, ← sub_smul, ← add_smul, ← sub_smul, h1, zero_smul]
  refine ⟨t, m, z, hz, ht, htχ, hm, fun _ => rfl, ?_⟩
  refine IsPairClass.unique (isPairClass_pairBr a χ)
    ⟨fun g => t (QuotientGroup.mk g), fun g => m fun i => QuotientGroup.mk (g i),
      (layerInf p K (MaximalUnramifiedExtension p K)).hom.f 2 z, by rw [← (layerInf p K (MaximalUnramifiedExtension p K)).hom.comm, hz, map_zero],
      ht.comp_continuous continuous_quot_mk, htχ, fun g => hm _, fun g => rfl, rfl⟩

theorem pairK_uniformiser_unr (hK : FiniteDimensional ℚ_[p] K) (π : Kˣ) (hπ : vK p K π = 1) (χ : charGrp (GK p K))
    (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) : pairK p K π χ = χ.1 (Additive.ofMul (frobK p K)) := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzm, h⟩ := exists_ur_cocycle π χ hχ
  have h1 : (eK p K : ℝ) * vbar p (urOfK p K π).1 = 1 := by
    have h2 := vOn_spec p K ⟨ofK p K (Additive.ofMul π), ofK_mem p K _⟩
    have h3 : vOn p K ⟨ofK p K (Additive.ofMul π), ofK_mem p K _⟩ = 1 := hπ
    rw [h3, Int.cast_one] at h2
    exact h2.symm
  unfold pairK
  rw [h, invBr_layerInf hK, isInv_invUr hK (urOfK p K π) t m z hz (ofK_mem p K _) h1 ht hm hzm]
  exact htχ (frobK p K)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

