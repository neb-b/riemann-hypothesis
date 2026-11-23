module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CardRootsBar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ActEqZeroOfQK
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExistsUnitOneAddGenerator
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial
open Formalism.MainNotions.N.PlaceLabelTeichmuller

namespace UpperTheory.GalC

attribute [local instance] GlobalTheory.PassOp.factGk GlobalTheory.PassOp.neZeroGk

theorem exists_unit_one_add_generator (D : D7) (hCen : GlobalTheory.Pass.CentralElt D) (i : D.nd.Loc) :
    ∃ z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))), ∀ F,
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F := by
  classical
  let zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) →
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose
  let z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    ∑ p, if goodVec D p then zc p else 0
  have hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv)) := by
    intro p
    obtain ⟨L, hnd, hall, he⟩ := (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec
    rw [he]
    congr 1
    have e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        L.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, GlobalTheory.PassOp.prod_plc _ L hnd]
    congr 1
    funext j
    rw [if_pos (hall j)]
  have hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0 := by
    rw [e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]
    show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact hp p
    · simp
  have hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
    Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm
  refine ⟨z, fun F => ?_⟩
  rw [hz]
  unfold NTypes.onMt
  rw [dite_eq_left (Subalgebra.smul_mem _ hcen _), dite_eq_left hcen, ← LinearMap.smul_apply, ← map_smul]
  rfl

theorem exists_tuple (D : D7) (μ : D.what₂.Tup) (j : ℕ) (F : D.what₂.Mt μ j) (hF : D.ntypes.onMt μ j D.ntypes.e0 F ≠ 0) :
    ∃ s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X], D.ntypes.goodTuple s ∧
      ∀ k v, D.ntypes.onMt μ j (ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (s k v))) F ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hF
  let ef := fun p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) =>
    fun kv => (⟨ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv))),
      GlobalTheory.CutAtGood.atPlace_mem_center D kv.1 kv.2 _ (D.ntypes.eSer_central kv.1 _)⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))))
  have ht : ∀ p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      tens (fun kv => ESer D kv (p kv)) = ((∏ kv, ef p kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        MonoidAlgebra ℂ (G0g D.nd)) := by
    intro p
    have hnd := (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).nodup_toList
    have hall : ∀ kv, kv ∈ (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList := fun kv => by simp
    have hprod : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
        ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))).prod =
        ((∏ kv, ef p kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) := by
      have hmap : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
          ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
          ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map (ef p)).map (Subalgebra.val _) := by
        rw [List.map_map]; rfl
      rw [hmap, ← map_list_prod (Subalgebra.val _), ← List.prod_toFinset (ef p) hnd]
      simp
    rw [← hprod]
    have e1 : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
        ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, GlobalTheory.PassOp.prod_plc _ _ hnd]
    congr 1
    funext q
    rw [if_pos (hall q)]
  have he : D.ntypes.e0 = ((∑ p, if goodVec D p then ∏ kv, ef p kv else 0 :
      ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) := by
    rw [e0_eq, eGood, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact ht p
    · rfl
  have onMt_coe (c : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
      D.ntypes.onMt μ j (c : MonoidAlgebra ℂ (G0g D.nd)) = D.ntypes.cenMt μ j c := by
    unfold NTypes.onMt
    rw [dite_eq_left c.2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [he, onMt_coe, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  split_ifs with hg
  · by_contra hc
    obtain ⟨k, v, h0⟩ := hcon (fun k v => Formalism.CyclotomicNorms.monicOf (p ⟨k, v⟩)) hg
    apply hc
    rw [← Finset.prod_erase_mul _ (ef p) (Finset.mem_univ ⟨k, v⟩), map_mul, Module.End.mul_apply]
    have hzero : D.ntypes.cenMt μ j (ef p ⟨k, v⟩) F = 0 := by
      rw [← onMt_coe]
      exact h0
    rw [hzero, map_zero]
  · rw [map_zero]; rfl

theorem exists_type (D : D7) (P : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (PI : D.naut.AV i) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ D.naut.typeV i PI) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X])
    (h1 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0) :
    ∃ τ ∈ P.kty i PI k v, (P.lz k).lab τ = f := by
  classical
  have hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)),
      Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0) ∈
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
    intro τ _
    split_ifs
    · exact GlobalTheory.CutAtGood.atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b
    · rw [GlobalTheory.CutAtGood.atPlace_zero]
      exact Subalgebra.zero_mem _
  have hsum : D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (∑ τ, ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0)) =
      ∑ τ, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0)) := by
    let a := fun τ => ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0)
    have hco : ∀ τ, a τ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := fun τ => hc τ (Finset.mem_univ _)
    have hcoe (c : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (c : MonoidAlgebra ℂ (G0g D.nd)) =
          D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) c := by
      unfold NTypes.onMt
      rw [dite_eq_left c.2]
    change D.ntypes.onMt _ _ (∑ τ, a τ) = ∑ τ, D.ntypes.onMt _ _ (a τ)
    have hval : (∑ τ, a τ) = ((∑ τ, (⟨a τ, hco τ⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))))) : MonoidAlgebra ℂ (G0g D.nd)) := by
      simp only [AddSubmonoidClass.coe_finsetSum]
    rw [hval, ← AddSubmonoidClass.coe_finsetSum, hcoe, map_sum]
    apply Finset.sum_congr rfl
    intro τ _
    exact (hcoe ⟨a τ, hco τ⟩).symm
  rw [P.eSer_eq k, GlobalTheory.CutAtGood.atPlace_sum, hsum, LinearMap.sum_apply] at h1
  obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hlab : (P.lz k).lab τ = f
  · rw [if_pos hlab] at hτ
    exact ⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩
  · exfalso
    apply hτ
    rw [if_neg hlab, GlobalTheory.CutAtGood.atPlace_zero]
    unfold NTypes.onMt
    rw [dite_eq_left (Subalgebra.zero_mem _)]
    have e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0 := rfl
    rw [e0, map_zero]
    rfl

theorem tuple_labels {D : D7} {s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]} (hg : D.ntypes.goodTuple s) (i : D.nd.Loc)
    (k : Fin 2) (v : D.nd.PlG k) :
    ((s k v).Monic ∧ (s k v).natDegree = D.R.r ∧ (s k v).coeff 0 ≠ 0) ∧ Squarefree (s k v) ∧
      ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ → ¬ (s k v).IsRoot (u : ZMod (D.host.g k)) := by
  obtain ⟨h1, h2⟩ := hg k
  refine ⟨h1.1 v, h1.2.1 v, fun u hu hr => ?_⟩
  obtain ⟨ℓ, hℓg, hℓ⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  have hℓne : ℓ ≠ D.host.g k := by omega
  have hmem : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ∈
      Formalism.CyclotomicNorms.rootsBar (s k v) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_monic_ne_zero (f := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))) (h1.1 v).1)]
    exact hr.map (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))
  rcases hu with rfl | rfl
  · exact h1.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl
  · exact h2.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl

theorem nc_of_type (D : D7) (Q : PairedCharacterCondition.Pend D) (hDZ : PairedCharacterCondition.admDZ Q) (h1 : SumRepresentations.adm1 D) (h0 : SumRepresentations.tie0 D) (i : D.nd.Loc) (PI : D.naut.AV i)
    {s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]} (hg : D.ntypes.goodTuple s)
    (hs : ∀ k v, ∃ τ ∈ Q.kty i PI k v, (Q.lz k).lab τ = s k v) (k : Fin 2) (w : PlE D.host)
    (hw : w ∈ placesOver D.host.E (D.host.g k)) : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locV i PI w) := by
  obtain ⟨v, hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  obtain ⟨τ, hτ, e⟩ := hs k v
  obtain ⟨-, a, b⟩ := tuple_labels hg i k v
  exact UpperTheory.GalS.nc_of_label Q hDZ h1 i k v PI τ hτ (e ▸ a) (e ▸ b) w hv

end UpperTheory.GalC
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
section
noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual NumberField IsDedekindDomain GlobalTheory.HeightCounting Alg

section Layer

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}


open Classical in
set_option maxHeartbeats 2000000 in
def ndCut (N : NData R H what₂) (keep : N.Loc → Prop) (Xs : ∀ i, Set (N.X i)) (ne : ∀ i, keep i → (Xs i).Nonempty) :
    NData R H what₂ :=
  { N with
    Loc := {i // keep i}
    locs := fun j w => (N.locs j w).subtype keep
    locs_mem := fun j w i => Finset.mem_subtype.trans (N.locs_mem j w i.1)
    l := fun i => @NData.l R H what₂ N i.1
    lPrime := fun i => @NData.lPrime R H what₂ N i.1
    j := fun i => @NData.j R H what₂ N i.1
    j_range := fun i => @NData.j_range R H what₂ N i.1
    mu := fun i => @NData.mu R H what₂ N i.1
    w := fun i => @NData.w R H what₂ N i.1
    w_l := fun i => @NData.w_l R H what₂ N i.1
    mu_w := fun i => @NData.mu_w R H what₂ N i.1
    w_tw := fun i => @NData.w_tw R H what₂ N i.1
    O := fun i => @NData.O R H what₂ N i.1
    instO := fun i => @NData.instO R H what₂ N i.1
    domO := fun i => @NData.domO R H what₂ N i.1
    dvrO := fun i => @NData.dvrO R H what₂ N i.1
    algO := fun i => @NData.algO R H what₂ N i.1
    finO := fun i => @NData.finO R H what₂ N i.1
    topO := fun i => @NData.topO R H what₂ N i.1
    trO := fun i => @NData.trO R H what₂ N i.1
    O_adic := fun i => @NData.O_adic R H what₂ N i.1
    O_complete := fun i => @NData.O_complete R H what₂ N i.1
    embK := fun i => @NData.embK R H what₂ N i.1
    embK_w := fun i => @NData.embK_w R H what₂ N i.1
    chi := fun i => @NData.chi R H what₂ N i.1
    chi_cont := fun i => @NData.chi_cont R H what₂ N i.1
    chi_def := fun i => @NData.chi_def R H what₂ N i.1
    s0 := fun i => @NData.s0 R H what₂ N i.1
    restNLevelExponent_of_odd := fun i => @NData.restNLevelExponent_of_odd R H what₂ N i.1
    restNLevelExponent_of_two := fun i => @NData.restNLevelExponent_of_two R H what₂ N i.1
    S := fun i => @NData.S R H what₂ N i.1
    Q := fun i => @NData.Q R H what₂ N i.1
    SQ_split := fun i => @NData.SQ_split R H what₂ N i.1
    SQ_disj := fun i => @NData.SQ_disj R H what₂ N i.1
    SQ_l := fun i => @NData.SQ_l R H what₂ N i.1
    S_def := fun i => @NData.S_def R H what₂ N i.1
    gam0 := fun i => @NData.gam0 R H what₂ N i.1
    locNd_chebotarevPlace_mem := fun i => @NData.locNd_chebotarevPlace_mem R H what₂ N i.1
    restN_tameGenerator_generates := fun i => @NData.restN_tameGenerator_generates R H what₂ N i.1
    chi_ram_Q := fun i => @NData.chi_ram_Q R H what₂ N i.1
    Bj := fun i => @NData.Bj R H what₂ N i.1
    acgBj := fun i => @NData.acgBj R H what₂ N i.1
    modBj := fun i => @NData.modBj R H what₂ N i.1
    freeBj := fun i => @NData.freeBj R H what₂ N i.1
    finBj := fun i => @NData.finBj R H what₂ N i.1
    X := fun i => Xs i.1
    finX := fun i => Fintype.ofFinite _
    neX := fun i => (ne i.1 i.2).to_subtype
    T := fun i => cutT (N.T i.1) (Xs i.1)
    T_local := fun i => by
      haveI := (ne i.1 i.2).to_subtype; haveI := N.T_local i.1
      exact cutT_local _ _
    T_sep := fun i x y h => by
      obtain ⟨f, hf, e⟩ := N.T_sep i.1 x.1 y.1 (fun k => h (Subtype.ext k))
      exact ⟨_, ⟨f, hf, rfl⟩, e⟩
    Mt := fun i => cutM (N.T i.1) (N.act i.1) (Xs i.1)
    acgMt := fun i => inferInstance
    modMt := fun i => inferInstance
    freeMt := fun i => cutM_free _ _ _
    finMt := fun i => inferInstance
    act := fun i => cutAct (N.T i.1) (N.act i.1) (Xs i.1)
    act_inj := fun i => cutAct_inj _ _ _ (N.T_sep i.1) (N.act_inj i.1)
    prMt := fun i => (qK (N.T i.1) (N.act i.1) (Xs i.1)).comp (N.prMt i.1)
    prMt_span := fun i => by
      have := congrArg (Submodule.map (qK (N.T i.1) (N.act i.1) (Xs i.1))) (N.prMt_span i.1)
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearMap.range_eq_top.2 (qK_surj _ _ _)] at this
      exact this
    prMt_lat := fun i => by
      have := congrArg (Submodule.map ((qK (N.T i.1) (N.act i.1) (Xs i.1)).restrictScalars (N.O i.1))) (N.prMt_lat i.1)
      rw [Submodule.map_span, ← Set.image_comp] at this
      refine Eq.trans this ?_
      ext v
      constructor
      · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
        exact ⟨_, (qK_tmul _ _ _ 1 m).symm⟩
      · rintro ⟨m, rfl⟩
        obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
        exact ⟨_, ⟨m, rfl⟩, qK_tmul _ _ _ 1 m⟩
    eig_ne := fun i x => Alg.eig_ne _ _ _ (N.T_sep i.1) x (N.eig_ne i.1 x.1)
    Z := fun i => (N.Z i.1).subtype _
    Zgood := fun i => (N.Zgood i.1).subtype _
    hT := fun i v k => resT _ _ (N.hT i.1 v k)
    T_gen := fun i => by
      have := congrArg (Subalgebra.map (resA (N.O i.1) (Xs i.1))) (N.T_gen i.1)
      rw [AlgHom.map_adjoin] at this
      refine Eq.trans (congrArg _ ?_) this
      ext f
      constructor
      · rintro ⟨v, k, a, b, c, d, e, g, rfl⟩
        exact ⟨_, ⟨v, k, a, b, c, d, e, g, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨v, k, a, b, c, d, e, g, rfl⟩, rfl⟩
        exact ⟨v, k, a, b, c, d, e, g, rfl⟩ }


open Classical in
def optIn {X : Type} (S : Set X) (o : Option X) : Option S := o.bind fun x => if h : x ∈ S then some ⟨x, h⟩ else none

theorem optIn_eq_some {X : Type} {S : Set X} {o : Option X} {x : S} : optIn S o = some x ↔ o = some x.1 := by
  cases o with
  | none => simp [optIn]
  | some y =>
    simp only [optIn, Option.bind_some, Option.some.injEq]
    split_ifs with h
    · simp [Subtype.ext_iff]
    · simp only [false_iff]; rintro rfl; exact h x.2


set_option maxHeartbeats 2000000 in
def nautCut {N : NData R H what₂} (A : NAut N) (keep : N.Loc → Prop) (Xs : ∀ i, Set (N.X i))
    (ne : ∀ i, keep i → (Xs i).Nonempty) : NAut (ndCut N keep Xs ne) :=
  { A with
    iotaQ := fun i => @NAut.iotaQ R H what₂ N A i.1
    iotaQC := fun i => @NAut.iotaQC R H what₂ N A i.1
    iota_LL := fun i => @NAut.iota_LL R H what₂ N A i.1
    iotaQ_alg := fun i => @NAut.iotaQ_alg R H what₂ N A i.1
    muC := fun i => @NAut.muC R H what₂ N A i.1
    muC_csd := fun i => @NAut.muC_csd R H what₂ N A i.1
    AV := fun i => @NAut.AV R H what₂ N A i.1
    finAV := fun i => @NAut.finAV R H what₂ N A i.1
    typeV := fun i => @NAut.typeV R H what₂ N A i.1
    typeV_ne := fun i => @NAut.typeV_ne R H what₂ N A i.1
    typeV_indep := fun i => @NAut.typeV_indep R H what₂ N A i.1
    typeV_top := fun i => @NAut.typeV_top R H what₂ N A i.1
    locV := fun i => @NAut.locV R H what₂ N A i.1
    satV := fun i => @NAut.satV R H what₂ N A i.1
    locV_unr := fun i => @NAut.locV_unr R H what₂ N A i.1
    infWt := fun i => @NAut.infWt R H what₂ N A i.1
    locW := fun i => @NAut.locW R H what₂ N A i.1
    satW := fun i => @NAut.satW R H what₂ N A i.1
    lab_loc := fun i => @NAut.lab_loc R H what₂ N A i.1
    wdOf := fun i => @NAut.wdOf R H what₂ N A i.1
    wdOf_dim := fun i => @NAut.wdOf_dim R H what₂ N A i.1
    wdOf_unr := fun i => @NAut.wdOf_unr R H what₂ N A i.1
    wdOf_frob := fun i => @NAut.wdOf_frob R H what₂ N A i.1
    wdOf_ine := fun i => @NAut.wdOf_ine R H what₂ N A i.1
    wdOf_mono0 := fun i => @NAut.wdOf_mono0 R H what₂ N A i.1
    IsCrysW := fun i => @NAut.IsCrysW R H what₂ N A i.1
    IsPotCrysW := fun i => @NAut.IsPotCrysW R H what₂ N A i.1
    IsdRW := fun i => @NAut.IsdRW R H what₂ N A i.1
    jumpsW := fun i => @NAut.jumpsW R H what₂ N A i.1
    wdOf_unrL := fun i => @NAut.wdOf_unrL R H what₂ N A i.1
    wdOf_mono0L := fun i => @NAut.wdOf_mono0L R H what₂ N A i.1
    jumpsInf := fun i => @NAut.jumpsInf R H what₂ N A i.1
    locAutHodgeTateWeightsLevelZero := fun i => @NAut.locAutHodgeTateWeightsLevelZero R H what₂ N A i.1
    jumpsInf_def := fun i => @NAut.jumpsInf_def R H what₂ N A i.1
    locAut_hodgeTateWeightsLevelZero_def := fun i => @NAut.locAut_hodgeTateWeightsLevelZero_def R H what₂ N A i.1
    chi_mu := fun i => @NAut.chi_mu R H what₂ N A i.1
    kFbar := fun i => @NAut.kFbar R H what₂ N A i.1
    ptV := fun i P => optIn (Xs i.1) (A.ptV i.1 P)
    pt_surj := fun i x => (A.pt_surj i.1 x.1).imp fun _ h => optIn_eq_some.2 h
    eig_dim := fun i x => by
      have e : {P | optIn (Xs i.1) (A.ptV i.1 P) = some x} = {P | A.ptV i.1 P = some x.1} := Set.ext fun _ => optIn_eq_some
      refine (mult_eq _ _ _ (N.T_sep i.1) x).trans ((A.eig_dim i.1 x.1).trans ?_)
      rw [← e]; rfl
    pt_loc := fun i P x h => A.pt_loc i.1 P x.1 (optIn_eq_some.1 h) }

end Layer


set_option maxHeartbeats 4000000 in
def layCut (D : D7) (c : CutD D) : Lay0 D :=
  { loc := D.loc, locA := D.locA, locT := D.locT
    nd := ndCut D.nd c.keep c.Xs c.ne
    ntw := { D.ntw with
      twOf := fun i => D.ntw.twOf i.1
      twSide := fun i => D.ntw.twSide i.1
      psiL := fun i => D.ntw.psiL i.1
      twOf_l := fun i => D.ntw.twOf_l i.1
      twist₂ := fun i => D.ntw.twist₂ i.1
      twO_emb := fun i => D.ntw.twO_emb i.1
      psiL_ord := fun i => D.ntw.psiL_ord i.1
      psiL_open := fun i => D.ntw.psiL_open i.1
      psiL_anti := fun i => D.ntw.psiL_anti i.1
      psiL_ram := fun i => D.ntw.psiL_ram i.1
      psiL_l := fun i => D.ntw.psiL_l i.1
      chi_tw := fun i => D.ntw.chi_tw i.1 }
    naut := nautCut D.naut c.keep c.Xs c.ne
    nbc := { D.nbc with
      embAV := fun i => D.nbc.embAV i.1
      embAV_inj := fun i => D.nbc.embAV_inj i.1
      embAV_loc := fun i => D.nbc.embAV_loc i.1
      embAV_sat := fun i => D.nbc.embAV_sat i.1
      embAV_sph := fun i => D.nbc.embAV_sph i.1
      embAV_inf := fun i => D.nbc.embAV_inf i.1 }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with
      heckeLoc_gamma_places := fun i => D.ntypes.heckeLoc_gamma_places i.1
      chiT_tg := fun i => D.ntypes.chiT_tg i.1 }
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    nth := { D.nth with }
    nbr := fun i => D.nbr i.1, nbr_ind := fun i => D.nbr_ind i.1, self_good := fun i => D.self_good i.1
    ntwbr := D.ntwbr, ntwbr_ind := D.ntwbr_ind
    loc_tie := fun i => D.loc_tie i.1, bc_tie := fun i => D.bc_tie i.1, rbar_tie := fun i => D.rbar_tie i.1
    mtpar_tie := fun i => D.mtpar_tie i.1 }

theorem layerCut_admissible (D : D7) (c : CutD D) : (layCut D c).ZOk := by
  classical
  have z : ∀ (i : {i // c.keep i}) (x : c.Xs i.1), x ∈ ZN (layCut D c).nd (layCut D c).naut i ↔ x.1 ∈ ZN D.nd D.naut i.1 :=
    fun i x => exists_congr fun P => and_congr optIn_eq_some Iff.rfl
  refine ⟨fun i x => ?_, fun i x => ?_⟩
  · exact (Finset.mem_subtype.trans (D.Z_tie i.1 x.1)).trans (z i x).symm
  · refine (Finset.mem_subtype.trans (D.Zgood_tie i.1 x.1)).trans (and_congr (z i x).symm ?_)
    exact exists_congr fun Sig => and_congr (exists_congr fun P => and_congr optIn_eq_some.symm Iff.rfl) Iff.rfl

def cut (D : D7) (c : CutD D) : D7 :=
  setRaw D (layCut D c).eta (layCut D c).eta_nonneg ((layCut D c).reEta _ (layCut D c).eta_nonneg)
    ((layerCut_admissible D c).reEta _ _) (layCut D c).etaOk_reEta

end UpperTheory.GalC
end
end

