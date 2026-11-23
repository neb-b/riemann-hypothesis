module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralSemidirectProductUnfolding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralParabolicUnfoldLevi
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc

theorem cavg_conj_KGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (k⁻¹ * x * k) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f x := by
  intro E _ _ n w f _ k hk x
  unfold GlobalTheory.LeviDesc.cavg
  rw [← GlobalTheory.TwOrbConj.avg_left (fun k' : GlobalTheory.LFun.KGL w (n := n) => f ((k' : GLw n w)⁻¹ * x * k')) ⟨k, hk⟩]
  congr 1
  funext k'
  congr 1
  simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
  group

theorem twistedOrbitalIntegral_parabolic_unfolding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk (Nat.add_sub_cancel' ha) w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, twOrb (MonoidHom.id (GlobalTheory.LeviDesc.parP a n w)) ((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ⟨_, hγ⟩ (fun p => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (p : GLw n w)) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f) := by
  intro E _ _ _ n a ha w f hf m hsep hγ
  obtain ⟨s, π, u, hs, hu, hπs, hinj, hker, hKs, hKπ, hKu⟩ := GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent E n a (n - a) (Nat.add_sub_cancel' ha) w
  have hγs : (⟨blk (Nat.add_sub_cancel' ha) w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) = s m := Subtype.ext (hs m).symm
  have hfin := GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m hsep hγ
  have hcent := _root_.GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  have hcpt := _root_.GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  rw [hγs] at hfin hcent hcpt ⊢
  have hrhs : GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f = fun m' => hint (intMat a (n - a) w) (fun X =>
      (fun p : GlobalTheory.LeviDesc.parP a n w => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (p : GLw n w)) ((u X)⁻¹ * s m' * u X)) := by
    funext m'
    unfold GlobalTheory.LeviDesc.orbN
    refine congrArg (hint (intMat a (n - a) w)) (funext fun X => ?_)
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
  rw [hrhs]
  refine _root_.GlobalTheory.Unfold.twOrb_unfold _ _ _ s π u hπs hinj hker _ _ (intMat a (n - a) w) hKs hKπ hKu m ?_ ?_ ?_ ?_ _ ?_ hfin
  · intro p
    rw [hcent]
    simp only [Subtype.ext_iff, hs]
  · intro p
    rw [hcpt]
    simp only [Subtype.ext_iff, hs]
  · intro q
    exact GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart E a (n - a) w m q
  · intro X
    obtain ⟨U, hU, hUi, hUk⟩ := GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral E n a (n - a) (Nat.add_sub_cancel' ha) w (Multiplicative.toAdd X)
    refine ⟨U, hU, hUi, fun k hk => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
    exact hUk k hk
  · intro k hk x
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact cavg_conj_KGL E n w f hf _ (Subgroup.mem_subgroupOf.1 hk) _

end GlobalTheory.LeviDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalTermEqFinprodLocalTerms
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

open GlobalTheory.BCT

theorem mem_map_conj_iff_term {G : Type} [Group G] (K : Subgroup G) (y z : G) :
    z ∈ K.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem cptPart_le_self_term {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T :=
  Subgroup.closure_le _ |>.mpr fun _ ht => ht.1

theorem inf_relIndex_of_le_left_term {G : Type} [Group G] {A B C : Subgroup G} (h : C ≤ A) :
    (A ⊓ B).relIndex C = B.relIndex C := by
  unfold Subgroup.relIndex
  congr 1
  ext ⟨c, hc⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact and_iff_right (h hc)

theorem avg_eq_one_of_forall_term {H : Type} [Group H] (u : H → ℂ) (hu : ∀ k, u k = 1) : avg u = 1 := by
  have hs : rStab u = ⊤ := by
    ext k; simp only [Subgroup.mem_top, iff_true]; intro x; rw [hu, hu]
  have hi : (rStab u).index = 1 := Subgroup.index_eq_one.2 hs
  have hsub : Subsingleton (H ⧸ rStab u) := by
    have hc : Nat.card (H ⧸ rStab u) = 1 := hi
    exact (Nat.card_eq_one_iff_unique.1 hc).1
  unfold avg
  rw [hi, finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ rStab u) (fun q hq => absurd (Subsingleton.elim q _) hq), hu]
  simp

theorem twTerm_eq_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v) → ∀ x, GlobalTheory.EulerAbs.twTerm θ (⨅ v, (K v).comap (pf v)) δ f x = ∏ᶠ v, GlobalTheory.EulerAbs.twTerm (θv v) (K v) (pf v δ) (fv v) (pf v x) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX θ θv hθ hK δ f fv hf hcomm hstab hwt hev x
  have hT : ∀ y, y ∈ twCent θ δ ↔ ∀ v, pf v y ∈ twCent (θv v) (pf v δ) := fun y => _root_.GlobalTheory.EulerAbs.mem_twCent_iff_forall_comp pf K hX θ θv hθ δ y
  have hC : ∀ y, y ∈ cptPart (twCent θ δ) ↔ ∀ v, pf v y ∈ cptPart (twCent (θv v) (pf v δ)) :=
    _root_.GlobalTheory.CptPartRestr.mem_cptPart_iff_forall pf K hX (twCent θ δ) (fun v => twCent (θv v) (pf v δ)) hT hcomm
  have hgood := hev.and (hX.eventually_mem x)
  have hCg : cptPart (twCent θ δ) = ⨅ v, (cptPart (twCent (θv v) (pf v δ))).comap (pf v) := by
    ext y; rw [hC, Subgroup.mem_iInf]; rfl
  have hHg : (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom =
      ⨅ v, ((K v).map (MulAut.conj (pf v x)).toMonoidHom).comap (pf v) := by
    ext y
    simp only [mem_map_conj_iff_term, Subgroup.mem_iInf, Subgroup.mem_comap, map_mul, map_inv]
  have hloc : ∀ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) = ((K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := fun v => inf_relIndex_of_le_left_term (cptPart_le_self_term _)
  have hCH : ∀ᶠ v in cofinite, cptPart (twCent (θv v) (pf v δ)) ≤ (K v).map (MulAut.conj (pf v x)).toMonoidHom :=
    hgood.mono fun v hv c hc => by
      rw [mem_map_conj_iff_term]
      exact mul_mem (mul_mem (inv_mem hv.2) (hv.1.2.2 hc)) hv.2
  have hrel : (twCent θ δ ⊓ (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom).relIndex
      (cptPart (twCent θ δ)) = ∏ᶠ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := by
    rw [inf_relIndex_of_le_left_term (cptPart_le_self_term _), hHg, hCg]
    simp only [hloc]
    exact GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod pf K hX (fun v => cptPart (twCent (θv v) (pf v δ)))
      (fun v => (K v).map (MulAut.conj (pf v x)).toMonoidHom)
      (fun v => by rw [← hloc]; exact (hwt v (pf v x)).2) hCH
  let u : ∀ v, K v → ℂ := fun v k => fv v ((pf v x * k)⁻¹ * pf v δ * θv v (pf v x * k))
  have hfun : (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩ := by
    funext k; rw [hf]; congr 1; funext v; simp only [u, map_mul, map_inv, hθ]
  have hu1 : ∀ᶠ v in cofinite, ∀ k, u v k = 1 := hgood.mono fun v hv k => by
    have hk : pf v x * (k : Y v) ∈ K v := mul_mem hv.2 k.2
    simp only [u]
    rw [hv.1.1, Set.indicator_of_mem (show _ ∈ (K v : Set (Y v)) from
      mul_mem (mul_mem (inv_mem hk) hv.1.2.1) (hK v _ hk))]
    rfl
  have havg : avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      ∏ᶠ v, avg (u v) := by
    rw [hfun]; exact _root_.GlobalTheory.AvgRestr.avg_restr_prod pf K hX u (fun v => hstab v (pf v x)) hu1
  have hfa : Function.HasFiniteMulSupport fun v => (((twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) : ℕ) : ℂ) :=
    (eventually_cofinite.1 hCH).subset fun v hv h => hv (by
      show ((_ : ℕ) : ℂ) = 1
      rw [hloc, Subgroup.relIndex_eq_one.2 h, Nat.cast_one])
  have hfb : Function.HasFiniteMulSupport fun v => avg (u v) :=
    (eventually_cofinite.1 hu1).subset fun v hv h => hv (avg_eq_one_of_forall_term _ h)
  unfold twTerm
  rw [hrel, havg, Nat.cast_finprod', ← finprod_mul_distrib hfa hfb]

end GlobalTheory.EulerAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasureTwo
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory

namespace GKConjScale

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_eq_ofAdd_ordL {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := by simpa using hx
  unfold ordL
  rw [dite_eq_right h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

theorem coe_mul_le_iff (g h : Multiplicative ℤ) (x : WithZero (Multiplicative ℤ)) :
    (g : WithZero (Multiplicative ℤ)) * x ≤ h ↔ x ≤ ((g⁻¹ * h : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro H
    calc x = ((g⁻¹ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * (g * x) := by
          rw [← mul_assoc, ← WithZero.coe_mul, inv_mul_cancel, WithZero.coe_one, one_mul]
      _ ≤ ((g⁻¹ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * h := by gcongr
      _ = _ := by rw [WithZero.coe_mul]
  · intro H
    calc (g : WithZero (Multiplicative ℤ)) * x ≤ g * ((g⁻¹ * h : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ = h := by rw [WithZero.coe_mul, ← mul_assoc, ← WithZero.coe_mul, mul_inv_cancel, WithZero.coe_one, one_mul]

variable {n : ℕ}

theorem inv_offdiag {σ : L →+* L} (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i j : Fin n) (hij : i ≠ j) :
    (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  rw [Subgroup.coe_inv, (GlobalTheory.LGrp.mem_GU_iff σ n _).1 t.2 i j,
    ht _ _ (fun h => hij (Fin.rev_injective h).symm), map_zero]


end GKConjScale

end GlobalTheory
end
end

