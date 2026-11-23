module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.RealPlaces.ConeDefs
public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.Bundle0002
public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CupLeibniz
public import GroundTheory.ProfiniteCohomology.CoinducedModules.Acyclic

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.RealPlaces.ConeHomotopy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

namespace LeibnizPairing

section Prod

variable {M₁ M₂ N₁ N₂ P₁ P₂ N : CochainComplex (ModuleCat.{u} k) ℕ}

noncomputable def prod (μ₁ : LeibnizPairing M₁ N₁ P₁) (μ₂ : LeibnizPairing M₂ N₂ P₂) :
    LeibnizPairing (prodComplex M₁ M₂) (prodComplex N₁ N₂) (prodComplex P₁ P₂) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : M₁.X r × M₂.X r) (y : N₁.X s × N₂.X s) =>
      (show (prodComplex P₁ P₂).X n from (μ₁.μ h x.1 y.1, μ₂.μ h x.2 y.2)))
    (fun _ _ _ => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (map_add _ _ _) (map_add _ _ _))
    (fun _ _ _ => Prod.ext (map_smul _ _ _) (map_smul _ _ _))
  leibniz {r s n} h x y := by
    rw [prodComplex_d_hom_apply, prodComplex_d_hom_apply, prodComplex_d_hom_apply]
    exact Prod.ext (μ₁.leibniz h x.1 y.1) (μ₂.leibniz h x.2 y.2)

noncomputable def prodLeft (μ₁ : LeibnizPairing M₁ N P₁) (μ₂ : LeibnizPairing M₂ N P₂) :
    LeibnizPairing (prodComplex M₁ M₂) N (prodComplex P₁ P₂) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : M₁.X r × M₂.X r) (y : N.X s) =>
      (show (prodComplex P₁ P₂).X n from (μ₁.μ h x.1 y, μ₂.μ h x.2 y)))
    (fun _ _ _ => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (map_add _ _ _) (map_add _ _ _))
    (fun _ _ _ => Prod.ext (map_smul _ _ _) (map_smul _ _ _))
  leibniz {r s n} h x y := by
    rw [prodComplex_d_hom_apply, prodComplex_d_hom_apply]
    exact Prod.ext (μ₁.leibniz h x.1 y) (μ₂.leibniz h x.2 y)

end Prod

section DegZero

variable {E E' : ModuleCat.{u} k} {N : CochainComplex (ModuleCat.{u} k) ℕ}

noncomputable def degZeroμ (β : E →ₗ[k] N.X 0 →ₗ[k] E') :
    ∀ (r s n : ℕ), r + s = n →
      (degZeroComplex E).X r →ₗ[k] N.X s →ₗ[k] (degZeroComplex E').X n
  | 0, 0, 0, _ => β
  | _, _, _, _ => 0

theorem degZeroμ_succ (β : E →ₗ[k] N.X 0 →ₗ[k] E') (r s n : ℕ) (h : r + (s + 1) = n) :
    degZeroμ β r (s + 1) n h = 0 := by
  cases r <;> cases n <;> rfl

noncomputable def degZero (β : E →ₗ[k] N.X 0 →ₗ[k] E') :
    LeibnizPairing (degZeroComplex E) N (degZeroComplex E') where
  μ {r s n} h := degZeroμ β r s n h
  leibniz {r s n} h x y := by
    rw [degZeroComplex_d, degZeroComplex_d, degZeroμ_succ]
    simp

end DegZero

section CoconeHtpy

variable {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  (μL : LeibnizPairing L N' L') (ρ : N ⟶ N') (μK : LeibnizPairing K N K')
  (η : ∀ {r s n : ℕ}, r + s = n → K.X r →ₗ[k] N.X s →ₗ[k] shiftNegOneX L' n)

noncomputable def coconeLeftHtpyμ {r s n : ℕ} (h : r + s = n) :
    (mappingCoconeNat f).X r →ₗ[k] N.X s →ₗ[k] (mappingCoconeNat f').X n :=
  LinearMap.mk₂ k
    (fun (p : K.X r × shiftNegOneX L r) z =>
      ((μK.μ h p.1 z, μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) :
        K'.X n × shiftNegOneX L' n))
    (fun p q z => Prod.ext (LinearMap.map_add₂ _ _ _ _) (by
      change μL.shiftLeft r s n h (p.2 + q.2) ((ρ.f s).hom z) + η h (p.1 + q.1) z = _
      rw [LinearMap.map_add₂, LinearMap.map_add₂]
      change _ = (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) +
        (μL.shiftLeft r s n h q.2 ((ρ.f s).hom z) + η h q.1 z)
      abel))
    (fun c p z => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (by
      change μL.shiftLeft r s n h (c • p.2) ((ρ.f s).hom z) + η h (c • p.1) z = _
      rw [LinearMap.map_smul₂, LinearMap.map_smul₂]
      change _ = c • (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z)
      rw [smul_add]))
    (fun p z z' => Prod.ext (map_add _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (z + z')) + η h p.1 (z + z') = _
      rw [map_add (f := _), map_add (f := _), map_add (f := _)]
      change _ = (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) +
        (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z') + η h p.1 z')
      abel))
    (fun c p z => Prod.ext (map_smul _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (c • z)) + η h p.1 (c • z) = _
      rw [map_smul, map_smul, map_smul]
      change _ = c • (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z)
      rw [smul_add]))

noncomputable def coconeLeftHtpy
    (hη : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
      shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) + (shiftNegOneD L' n).hom (η h x z) =
        shiftNegOneSucc L' n (μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) +
          η (by omega) ((K.d r (r + 1)).hom x) z +
          (-1 : k) ^ r • η (by omega) x ((N.d s (s + 1)).hom z)) :
    LeibnizPairing (mappingCoconeNat f) N (mappingCoconeNat f') where
  μ h := coconeLeftHtpyμ μL ρ μK η h
  leibniz {r s n} h p z := by
    revert p
    intro (p : K.X r × shiftNegOneX L r)
    obtain ⟨x, y⟩ := p
    rw [mappingCoconeNat_d, mappingCoconeNat_d]
    refine Prod.ext (μK.leibniz h x z) ?_
    change shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) +
        (shiftNegOneD L' n).hom (μL.shiftLeft r s n h y ((ρ.f s).hom z) + η h x z) =
      (μL.shiftLeft (r + 1) s (n + 1) (by omega)
          (shiftNegOneSucc L r ((f.f r).hom x) + (shiftNegOneD L r).hom y) ((ρ.f s).hom z) +
        η (by omega) ((K.d r (r + 1)).hom x) z) +
        (-1 : k) ^ r • (μL.shiftLeft r (s + 1) (n + 1) (by omega) y
          ((ρ.f (s + 1)).hom ((N.d s (s + 1)).hom z)) + η (by omega) x ((N.d s (s + 1)).hom z))
    have key := eq_sub_of_add_eq' (hη h x z)
    rw [← hom_apply_hom_apply_eq_of_comp_eq (ρ.comm s (s + 1)) z, map_add (f := _), key,
      shiftLeft_leibniz, LinearMap.map_add₂, shiftLeft_succ, smul_add]
    abel

variable (hη : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
  shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) + (shiftNegOneD L' n).hom (η h x z) =
    shiftNegOneSucc L' n (μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) +
      η (by omega) ((K.d r (r + 1)).hom x) z +
      (-1 : k) ^ r • η (by omega) x ((N.d s (s + 1)).hom z))

theorem coconeLeftHtpy_homology_homologyδ {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : L.homology r) (z : N.homology s) :
    (coconeLeftHtpy μL ρ μK η hη).homology h' ((mappingCoconeNat.homologyδ f r).hom ξ) z =
      (mappingCoconeNat.homologyδ f' n).hom
        (μL.homology h ξ ((HomologicalComplex.homologyMap ρ s).hom z)) := by
  obtain ⟨c, rfl⟩ := homologyπ_hom_surjective _ r ξ
  obtain ⟨w, rfl⟩ := homologyπ_hom_surjective _ s z
  obtain ⟨c', hc'1, hc'2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f r c
  rw [homologyMap_homologyπ_apply, homology_homologyπ]
  obtain ⟨c'', hc''1, hc''2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f' n
    (μL.cycles h c ((HomologicalComplex.cyclesMap ρ s).hom w))
  rw [hc'1, hc''1, homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cycles, hc'2, hc''2, iCycles_cycles, iCycles_cyclesMap_apply]
  refine Prod.ext (LinearMap.map_zero₂ _ _) ?_
  change μL.shiftLeft (r + 1) s (n + 1) h' _ _ + η h' 0 _ = _
  rw [LinearMap.map_zero₂, add_zero]
  rfl

end CoconeHtpy

end LeibnizPairing

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.RealPlaces.NormHomotopy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology

universe u

section Tuple

variable {α : Type*}

def consTuple {s m : ℕ} (h : s = m + 1) (a : α) (g : Fin m → α) : Fin s → α :=
  fun i => if hi : (i : ℕ) = 0 then a else g ⟨i - 1, by omega⟩

theorem consTuple_rfl {m : ℕ} (a : α) (g : Fin m → α) :
    consTuple (rfl : m + 1 = m + 1) a g = Fin.cons a g := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consTuple]
  · simp only [consTuple, Fin.val_succ, Nat.add_one_ne_zero, dite_false, Fin.cons_succ]
    congr 1

theorem continuous_consTuple [TopologicalSpace α] {s m : ℕ} (h : s = m + 1) (a : α) :
    Continuous (consTuple h a) := by
  refine continuous_pi fun i => ?_
  unfold consTuple
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

end Tuple

section Homotopy

variable {k F : Type u} [CommRing k] [Group F] [Fintype F] {X Y Z : Rep.{u} k F}
  (μ : X ⊗ Y ⟶ Z)

noncomputable def normHomotopyFun {s m : ℕ} (h : s = m + 1) (e : X) (y : (Fin s → F) → Y) : (Fin m → F) → Z :=
  fun g => ∑ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] y (consTuple h a⁻¹ g) : (X ⊗ Y : Rep k F))))

theorem normHomotopyFun_add_left {s m : ℕ} (h : s = m + 1) (e e' : X) (y : (Fin s → F) → Y) :
    normHomotopyFun μ h (e + e') y = normHomotopyFun μ h e y + normHomotopyFun μ h e' y := by
  funext g
  simp only [normHomotopyFun, Pi.add_apply, TensorProduct.add_tmul, map_add (f := _),
    Finset.sum_add_distrib]

theorem normHomotopyFun_smul_left {s m : ℕ} (h : s = m + 1) (c : k) (e : X) (y : (Fin s → F) → Y) :
    normHomotopyFun μ h (c • e) y = c • normHomotopyFun μ h e y := by
  funext g
  simp only [normHomotopyFun, Pi.smul_apply, ← TensorProduct.smul_tmul', map_smul, Finset.smul_sum]

theorem normHomotopyFun_add_right {s m : ℕ} (h : s = m + 1) (e : X) (y y' : (Fin s → F) → Y) :
    normHomotopyFun μ h e (y + y') = normHomotopyFun μ h e y + normHomotopyFun μ h e y' := by
  funext g
  simp only [normHomotopyFun, Pi.add_apply, TensorProduct.tmul_add, map_add (f := _),
    Finset.sum_add_distrib]

theorem normHomotopyFun_smul_right {s m : ℕ} (h : s = m + 1) (c : k) (e : X)
    (y : (Fin s → F) → Y) :
    normHomotopyFun μ h e (c • y) = c • normHomotopyFun μ h e y := by
  funext g
  simp only [normHomotopyFun, Pi.smul_apply, TensorProduct.tmul_smul, map_smul, Finset.smul_sum]

theorem sum_ρ_μ_tmul_ρ_inv (e : X) (b : Y) :
    ∑ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F)))) =
      μ.hom ((X.ρ.norm e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := by
  have h1 : ∀ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F)))) =
      μ.hom ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := fun a => by
    have h2 : ((X ⊗ Y).ρ a) ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F))) =
        ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := by
      change TensorProduct.map (X.ρ a) (Y.ρ a) (e ⊗ₜ[k] Y.ρ a⁻¹ b) = _
      rw [TensorProduct.map_tmul, Representation.self_inv_apply]
    exact (Rep.hom_comm_apply μ a _).symm.trans (congrArg _ h2)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl fun a _ => h1 a, ← map_sum, ← TensorProduct.sum_tmul]
  congr 2
  simp [Representation.norm]

theorem normHomotopyFun_d_add {m : ℕ} (e : X) (y : (Fin (m + 1) → F) → Y) :
    (inhomogeneousCochains.d Z m).hom (normHomotopyFun μ rfl e y) +
        normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y (m + 1)).hom y) =
      fun g => μ.hom ((X.ρ.norm e ⊗ₜ[k] y g : (X ⊗ Y : Rep k F))) := by
  funext g
  have hdy : ∀ a : F, (inhomogeneousCochains.d Y (m + 1)).hom y (Fin.cons a⁻¹ g) =
      Y.ρ a⁻¹ (y g) - y (Fin.cons (a⁻¹ * g 0) fun i => g i.succ) +
        ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) •
          y (Fin.cons a⁻¹ (Fin.contractNth j (· * ·) g)) := by
    intro a
    rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.cons_zero, Fin.cons_succ, contractNth_zero_cons, contractNth_succ_cons,
      Fin.val_zero, Fin.val_succ, zero_add, pow_one, neg_one_smul]
    have e2 : ∀ j : Fin (m + 1), (j : ℕ) + 1 + 1 = (j : ℕ) + 2 := fun _ => rfl
    simp only [e2]
    abel
  have hsplit : normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y (m + 1)).hom y) g =
      μ.hom ((X.ρ.norm e ⊗ₜ[k] y g : (X ⊗ Y : Rep k F))) -
        Z.ρ (g 0) (normHomotopyFun μ rfl e y fun i => g i.succ) +
        ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) •
          normHomotopyFun μ rfl e y (Fin.contractNth j (· * ·) g) := by
    simp only [normHomotopyFun, consTuple_rfl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hdy, TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul, map_add, map_sub, map_sum, map_smul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [sum_ρ_μ_tmul_ρ_inv μ e (y g), Finset.sum_comm (β := Z.V)]
    congr 2
    · refine (Fintype.sum_equiv (Equiv.mulLeft (g 0)) _ _ fun a => ?_).symm
      simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right, map_mul,
        Module.End.mul_apply]
    · funext j
      rw [Finset.smul_sum]
  rw [Pi.add_apply, inhomogeneousCochains.d_hom_apply, hsplit]
  have hpow : ∀ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) = -(-1 : k) ^ ((j : ℕ) + 1) :=
    fun j => by rw [pow_succ, mul_neg_one]
  simp only [hpow, neg_smul, Finset.sum_neg_distrib]
  abel

theorem normHomotopyFun_d_zero (e : X) (z : (Fin 0 → F) → Y) :
    normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y 0).hom z) =
      fun g => μ.hom ((X.ρ.norm e ⊗ₜ[k] z g : (X ⊗ Y : Rep k F))) -
        Z.ρ.norm (μ.hom ((e ⊗ₜ[k] z g : (X ⊗ Y : Rep k F)))) := by
  funext g
  set b := z g with hb
  have hzc : z = fun _ => b := funext fun g' => congrArg z (Subsingleton.elim g' g)
  rw [hzc]
  simp only [normHomotopyFun, inhomogeneousCochains.d_hom_apply, consTuple_rfl, Fin.cons_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, zero_add, pow_one,
    neg_one_smul, ← sub_eq_add_neg,
    TensorProduct.tmul_sub, map_sub, Finset.sum_sub_distrib]
  rw [sum_ρ_μ_tmul_ρ_inv]
  congr 1
  simp [Representation.norm]

end Homotopy

section LocallyConstant

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [Fintype F] {X Y Z : Rep.{u} k F} [IsDiscreteRep X] [IsDiscreteRep Y] [IsDiscreteRep Z]
  (μ : X ⊗ Y ⟶ Z)

omit [IsTopologicalGroup F] [IsDiscreteRep X] [IsDiscreteRep Y] [IsDiscreteRep Z] in
theorem isLocallyConstant_normHomotopyFun {s m : ℕ} (h : s = m + 1) (e : X)
    {y : (Fin s → F) → Y} (hy : IsLocallyConstant y) :
    IsLocallyConstant (normHomotopyFun μ h e y) := by
  have e1 : normHomotopyFun μ h e y = ∑ a : F, fun g =>
      Z.ρ a (μ.hom ((e ⊗ₜ[k] y (consTuple h a⁻¹ g) : (X ⊗ Y : Rep k F)))) := by
    funext g
    simp [normHomotopyFun, Finset.sum_apply]
  rw [e1]
  exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb)
    (IsLocallyConstant.const 0) fun a _ =>
      (hy.comp_continuous (continuous_consTuple h a⁻¹)).comp
        (fun b : Y => Z.ρ a (μ.hom ((e ⊗ₜ[k] b : (X ⊗ Y : Rep k F)))))

noncomputable def normHomotopy {s m : ℕ} (h : s = m + 1) :
    X →ₗ[k] (cochainsComplex Y).X s →ₗ[k] (cochainsComplex Z).X m :=
  LinearMap.mk₂ k (fun e y => mkCochain Z (normHomotopyFun μ h e (cochainOf Y y))
      (isLocallyConstant_normHomotopyFun μ h e (isLocallyConstant_cochainOf y)))
    (fun e e' _ => cochainOf_injective (normHomotopyFun_add_left μ h e e' _))
    (fun c e _ => cochainOf_injective (normHomotopyFun_smul_left μ h c e _))
    (fun e _ _ => cochainOf_injective (normHomotopyFun_add_right μ h e _ _))
    (fun c e _ => cochainOf_injective (normHomotopyFun_smul_right μ h c e _))

omit [IsDiscreteRep X] in
theorem cochainOf_normHomotopy {s m : ℕ} (h : s = m + 1) (e : X) (y : (cochainsComplex Y).X s) :
    cochainOf Z (normHomotopy μ h e y) = normHomotopyFun μ h e (cochainOf Y y) :=
  rfl


omit [Fintype F] in
theorem cochainOf_cupPairingCochains_zeroCochain {n : ℕ} (x : X) (y : (cochainsComplex Y).X n)
    (g : Fin n → F) :
    cochainOf Z (cupPairingCochains μ (zero_add n) (zeroCochain X x) y) g =
      μ.hom ((x ⊗ₜ[k] cochainOf Y y g : (X ⊗ Y : Rep k F))) := by
  rw [cochainOf_cupPairingCochains]
  change μ.hom (GroupCoh.cupCochain _ _ _ g) = _
  rw [GroupCoh.cupCochain_apply]
  congr 2
  have hp : Fin.partialProd g ⟨0, by omega⟩ = 1 := Fin.partialProd_zero g
  rw [hp, map_one, Module.End.one_apply]
  congr 1
  funext j
  congr 1
  exact Fin.ext (zero_add _)

theorem d_normHomotopy_add {m : ℕ} (e : X) (y : (cochainsComplex Y).X (m + 1)) :
    ((cochainsComplex Z).d m (m + 1)).hom (normHomotopy μ rfl e y) +
        normHomotopy μ rfl e (((cochainsComplex Y).d (m + 1) (m + 1 + 1)).hom y) =
      cupPairingCochains μ (zero_add (m + 1)) (zeroCochain X (X.ρ.norm e)) y := by
  apply cochainOf_injective
  rw [cochainOf_add, cochainOf_d, cochainOf_normHomotopy, cochainOf_normHomotopy, cochainOf_d,
    normHomotopyFun_d_add]
  funext g
  rw [cochainOf_cupPairingCochains_zeroCochain]

theorem normHomotopy_d_zero (e : X) (z : (cochainsComplex Y).X 0) :
    normHomotopy μ rfl e (((cochainsComplex Y).d 0 1).hom z) =
      cupPairingCochains μ (zero_add 0) (zeroCochain X (X.ρ.norm e)) z -
        zeroCochain Z (Z.ρ.norm (μ.hom ((e ⊗ₜ[k] cochainOf Y z (fun i => i.elim0) :
          (X ⊗ Y : Rep k F))))) := by
  apply cochainOf_injective
  rw [cochainOf_normHomotopy, cochainOf_d, normHomotopyFun_d_zero]
  funext g
  have hg : g = fun i => i.elim0 := Subsingleton.elim _ _
  subst hg
  rw [show ∀ a b : (cochainsComplex Z).X 0, cochainOf Z (a - b) = cochainOf Z a - cochainOf Z b
    from fun _ _ => rfl, Pi.sub_apply, cochainOf_cupPairingCochains_zeroCochain]
  rfl

end LocallyConstant

end GroundTheory.ProfCoh
end

