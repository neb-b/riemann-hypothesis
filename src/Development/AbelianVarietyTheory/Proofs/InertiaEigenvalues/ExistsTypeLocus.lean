module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051

@[expose] public section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
open Polynomial

namespace GlobalTheory.CutAtGood

section AtPlace

attribute [local instance] Formalism.BasicNotions.Examples₂.NZ.neZero_g Formalism.BasicNotions.Examples₂.NZ.fact_g Classical.propDecidable

variable (D : D7)

theorem atPlace_add (k : Fin 2) (v : D.nd.PlG k) (a b : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (a + b) = Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a + Formalism.MainNotions.ArithmeticCylinders.atPlace D k v b := by
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  rw [MonoidAlgebra.coeff_add, Finsupp.mapDomain_add, MonoidAlgebra.ofCoeff_add]

theorem atPlace_zero (k : Fin 2) (v : D.nd.PlG k) : Formalism.MainNotions.ArithmeticCylinders.atPlace D k v 0 = 0 := by
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  rw [MonoidAlgebra.coeff_zero, Finsupp.mapDomain_zero, MonoidAlgebra.ofCoeff_zero]

theorem atPlace_sum (k : Fin 2) (v : D.nd.PlG k) {ι : Type} (S : Finset ι)
    (a : ι → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (∑ i ∈ S, a i) = ∑ i ∈ S, Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, atPlace_zero]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, atPlace_add, ih]

theorem atPlace_eq_tens (k : Fin 2) (v : D.nd.PlG k)
    (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a = Formalism.BasicNotions.Examples₂.NZ.tens
      (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      (Function.update (fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
        (1 : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))))) ⟨k, v⟩ a) := by
  classical
  have hinj : Function.Injective (Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
      GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k)) := by
    intro x y h
    have := congrFun h ⟨k, v⟩
    rwa [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same] at this
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [Formalism.BasicNotions.Examples₂.NZ.tens_coeff]
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  rw [MonoidAlgebra.coeff_ofCoeff]
  by_cases hg : g ∈ Set.range (Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
      GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k))
  · obtain ⟨h, rfl⟩ := hg
    rw [Finsupp.mapDomain_apply_of_injective hinj, Fintype.prod_eq_single (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k)
      (fun i hi => by rw [Function.update_of_ne hi, Pi.mulSingle_eq_of_ne hi, MonoidAlgebra.coeff_one_one]),
      Function.update_self, Pi.mulSingle_eq_same]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hg]
    have hex : ∃ i, i ≠ (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k) ∧ g i ≠ 1 := by
      by_contra hc
      simp only [not_exists, not_and, not_not] at hc
      apply hg
      refine ⟨g ⟨k, v⟩, funext fun i => ?_⟩
      by_cases hi : i = ⟨k, v⟩
      · subst hi
        rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hi, hc i hi]
    obtain ⟨i, hi, hgi⟩ := hex
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [Function.update_of_ne hi, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      ite_eq_right (Ne.symm hgi)]

theorem atPlace_one (k : Fin 2) (v : D.nd.PlG k) : Formalism.MainNotions.ArithmeticCylinders.atPlace D k v 1 = 1 := by
  classical
  have hu : Function.update (fun kv : (Σ k : Fin 2, D.nd.PlG k) =>
      (1 : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))))) ⟨k, v⟩ 1 = fun _ => 1 :=
    Function.update_eq_self_iff.mpr rfl
  rw [atPlace_eq_tens, hu]
  exact Formalism.BasicNotions.Examples₂.NZ.tens_single (k := ℂ) 1

theorem atPlace_mem_center (k : Fin 2) (v : D.nd.PlG k)
    (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (ha : ∀ b, a * b = b * a) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
  classical
  rw [Subalgebra.mem_center_iff, atPlace_eq_tens]
  intro b
  refine (Formalism.BasicNotions.Examples₂.NZ.tens_central _ (fun i c => ?_) b).symm
  rcases eq_or_ne i ⟨k, v⟩ with rfl | hi
  · rw [Function.update_self]
    exact ha c
  · rw [Function.update_of_ne hi, one_mul, mul_one]

end AtPlace

section OnMt

variable (D : D7) (μ : D.what₂.Tup) (j : ℕ)

local notation "CZ" => Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))

theorem onMt_add {a b : MonoidAlgebra ℂ (G0g D.nd)} (ha : a ∈ CZ) (hb : b ∈ CZ) :
    D.ntypes.onMt μ j (a + b) = D.ntypes.onMt μ j a + D.ntypes.onMt μ j b := by
  unfold NTypes.onMt
  rw [dite_eq_left (Subalgebra.add_mem _ ha hb), dite_eq_left ha, dite_eq_left hb]
  exact map_add (D.ntypes.cenMt μ j) ⟨a, ha⟩ ⟨b, hb⟩

theorem onMt_one : D.ntypes.onMt μ j 1 = 1 := by
  unfold NTypes.onMt
  rw [dite_eq_left (Subalgebra.one_mem _)]
  exact map_one (D.ntypes.cenMt μ j)

theorem onMt_sum {ι : Type} (S : Finset ι) (a : ι → MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ i ∈ S, a i ∈ CZ) :
    D.ntypes.onMt μ j (∑ i ∈ S, a i) = ∑ i ∈ S, D.ntypes.onMt μ j (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    unfold NTypes.onMt
    rw [Finset.sum_empty, Finset.sum_empty, dite_eq_left (Subalgebra.zero_mem _)]
    exact map_zero (D.ntypes.cenMt μ j)
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      onMt_add D μ j (ha i (Finset.mem_insert_self i S))
        (Subalgebra.sum_mem _ fun x hx => ha x (Finset.mem_insert_of_mem hx)),
      ih fun x hx => ha x (Finset.mem_insert_of_mem hx)]

end OnMt

section Record

variable {D : D7}

theorem isoLoc_perm {Pa Pb : List (Part D.naut.CG)} (h : Pa.Perm Pb) (w : PlE D.host) :
    isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pb w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons p _ ih => simp only [List.foldr_cons, ih]
  | swap p q l =>
    simp only [List.foldr_cons]
    rw [← D.naut.lpSum_assoc, D.naut.lpSum_comm (spehLoc D.nd D.naut q w), D.naut.lpSum_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem locG_tw_back (hL : Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    D.naut.locG (D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv) w = D.naut.locG π w := by
  obtain ⟨h1, h2⟩ := D.naut.etaTinv_def w
  have d1 := D.naut.locG_dim D.naut.etaTinv w
  have d2 := D.naut.locG_dim D.naut.etaT w
  have hu2 := D.naut.etaT_unr w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card _ hu2).trans d2)
  have hc0 : c ≠ 0 := by
    have := D.naut.frobEig_ne_zero _ hu2
    rw [hc] at this
    simpa [eq_comm] using this
  have hc' : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {c⁻¹} := by
    rw [h2, hc, Multiset.map_singleton]
  have hu := D.naut.unr_char _ _ d1 hu2 h1
  have hf : D.naut.frobEig (D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w)) = {1} := by
    rw [D.naut.frobEig_char _ _ c⁻¹ hu2 h1 d1 hc', hc]
    simp [hc0]
  have he : D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w) = D.naut.lpUnr w {1} := by
    rw [D.naut.unr_eq_lpUnr _ hu, hf]
  obtain ⟨-, -, -, e1, e2, -⟩ := hL w (D.naut.locG π w) (D.naut.locG π w) (D.naut.locG D.naut.etaT w)
    (D.naut.locG D.naut.etaTinv w) 0 d2 d1
  rw [D.naut.locG_tw, D.naut.locG_tw, e1, he, e2]

theorem isBCV_perm {i : D.nd.Loc} {P : D.naut.AV i} {Pa Pa' : List (Part D.naut.CG)}
    (h : IsBCV D.nd D.naut i P Pa) (hp : Pa.Perm Pa') : IsBCV D.nd D.naut i P Pa' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun p hp' => h1 p (hp.mem_iff.2 hp'), (hp.map _).nodup_iff.1 h2, ?_, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_⟩
  · unfold rankIso at h3 ⊢
    rw [← (hp.map _).sum_eq]
    exact h3
  · rw [← isoLoc_perm hp w]
    exact h4 w hw
  · rw [← isoLoc_perm hp w]
    exact h5 w hw
  · unfold isoInf at h6 ⊢
    rw [← (hp.map _).sum_eq]
    exact h6 τ

theorem typeV_le_mtPar {i : D.nd.Loc} {PI : D.naut.AV i} {Sig : List (Part D.naut.CG)} {σ' : D.ntypes.Par}
    (hσ : ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w)
    (hB : IsBCV D.nd D.naut i PI (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)) :
    D.naut.typeV i PI ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
  rw [D.mtpar_tie i σ']
  exact le_iSup₂_of_le (f := fun P _ => D.naut.typeV i P) PI ⟨Sig, fun w => (hσ w).symm, hB⟩ le_rfl

theorem tw_tw (hT0 : SumRepresentations.tie0 D) (h5 : SumRepresentations.adm5 D) {a : ℕ} (π : D.naut.CG a) (ha : 1 ≤ a) :
    D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π := by
  have hloc : ∀ w, D.naut.locG (D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv) w = D.naut.locG π w :=
    fun w => locG_tw_back hT0.1 π w
  have hp := h5.1 [⟨a, D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      simp only [isoLoc, spehLoc, List.foldr_cons, List.foldr_nil, hloc])
  have hpp := List.singleton_perm_singleton.1 hp
  exact eq_of_heq (Formalism.BasicNotions.Part.mk.inj hpp).2.1

theorem hasParamX_of_Z (hT0 : SumRepresentations.tie0 D) (h5 : SumRepresentations.adm5 D) {i : D.nd.Loc} {x : D.nd.X i}
    (hx : x ∈ D.nd.Z i) : ∃ Sig, HasParamX D.nd D.naut i x Sig := by
  classical
  obtain ⟨P1, hP1, Pa, hB, hm⟩ := (D.Z_tie i x).1 hx
  refine ⟨twistIso D.nd D.naut (Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩) D.naut.etaT,
    P1, hP1, isBCV_perm hB ?_⟩
  have hid : ∀ p ∈ Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩,
      (⟨p.a, D.naut.tw (D.naut.tw p.π D.naut.etaT) D.naut.etaTinv, p.d⟩ : Part D.naut.CG) = p := by
    intro p hp
    have hpa := (hB.1 p (List.mem_of_mem_erase hp)).1
    obtain ⟨pa, pπ, pd⟩ := p
    simp only [tw_tw hT0 h5 pπ hpa]
  have e : twistIso D.nd D.naut (twistIso D.nd D.naut (Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩)
      D.naut.etaT ++ [muPart D.nd D.naut i]) D.naut.etaTinv =
      Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ ++
        [⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩] := by
    unfold twistIso muPart
    rw [List.map_append, List.map_map]
    refine congrArg₂ (· ++ ·) ?_ rfl
    calc _ = List.map id (Pa.erase ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩) :=
          List.map_congr_left fun p hp => hid p hp
      _ = _ := List.map_id _
  rw [e]
  exact (List.perm_cons_erase hm).trans (List.perm_append_singleton _ _).symm

theorem labPar_eq {σ' : D.ntypes.Par} {Sig : List (Part D.naut.CG)}
    (hσ : ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w) (k : Fin 2) (v : D.nd.PlG k) :
    D.ntypes.labPar k σ' v = D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) := by
  rw [D.ntypes.labPar_def, hσ]

theorem goodSig_of_labels {Sig Sig' : List (Part D.naut.CG)}
    (h : ∀ k v, D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) =
      D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig' (D.naut.plGw k v)))
    (hg : goodSig D.nd D.naut Sig) : goodSig D.nd D.naut Sig' := by
  intro k
  have e : (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig' (D.naut.plGw k v))) =
      (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) :=
    funext fun v => (h k v).symm
  have := hg k
  simp only [e] at this ⊢
  exact this

theorem good_labels {Sig : List (Part D.naut.CG)} (hg : goodSig D.nd D.naut Sig) (i : D.nd.Loc) (k : Fin 2)
    (v : D.nd.PlG k) :
    Squarefree (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) ∧
      ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
        ¬ (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).IsRoot
          (u : ZMod (D.host.g k)) := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2⟩ := hg k
  refine ⟨h1.2.1 v, fun u hu hr => ?_⟩
  obtain ⟨ℓ, hℓg, hℓ⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  have hℓne : ℓ ≠ D.host.g k := by omega
  have hmem : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ∈
      Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_monic_ne_zero (h1.1 v).1)]
    exact hr.map (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))
  rcases hu with rfl | rfl
  · exact h1.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl
  · exact h2.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl

end Record

section Series

variable {D : D7}

local notation "CZ" => Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))

theorem eSer_mem (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f) ∈ CZ :=
  atPlace_mem_center D k v _ (D.ntypes.eSer_central k f)

theorem onMt_coe (μ : D.what₂.Tup) (j : ℕ) (c : ↥CZ) :
    D.ntypes.onMt μ j (c : MonoidAlgebra ℂ (G0g D.nd)) = D.ntypes.cenMt μ j c := by
  unfold NTypes.onMt
  rw [dite_eq_left c.2]

theorem series_fix (hSer : GlobalTheory.TypeLeaf.SerLoc D) (i : D.nd.Loc) (σ' : D.ntypes.Par)
    (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (hF : F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ')
    (k : Fin 2) (v : D.nd.PlG k) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (D.ntypes.labPar k σ' v))) F = F := by
  classical
  obtain ⟨S, -, hsum⟩ := D.ntypes.eSer_sum k
  have h1 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v 1) F = F := by
    rw [atPlace_one, onMt_one]
    rfl
  rw [← hsum, atPlace_sum, onMt_sum D _ _ S _ (fun f _ => eSer_mem k v f), LinearMap.sum_apply] at h1
  have hz : ∀ f, f ≠ D.ntypes.labPar k σ' v →
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F = 0 := by
    intro f hf
    by_contra hne
    exact hf (hSer i σ' k v f F hF hne)
  by_cases hm : D.ntypes.labPar k σ' v ∈ S
  · rw [Finset.sum_eq_single_of_mem _ hm (fun f _ hf => hz f hf)] at h1
    exact h1
  · rw [Finset.sum_eq_zero (fun f hf => hz f (fun h => hm (h ▸ hf)))] at h1
    rw [← h1, map_zero]

def ef (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X]) (kv : Σ k : Fin 2, D.nd.PlG k) : ↥CZ :=
  ⟨Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv)), eSer_mem kv.1 kv.2 (s kv)⟩

theorem list_prod_eq (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X])
    (L : List (Σ k : Fin 2, D.nd.PlG k)) (hnd : L.Nodup) (hall : ∀ kv, kv ∈ L) :
    (L.map fun kv => Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod =
      ((∏ kv, ef s kv : ↥CZ) : MonoidAlgebra ℂ (G0g D.nd)) := by
  classical
  have h1 : (L.map fun kv => Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))) =
      (L.map (ef s)).map (Subalgebra.val CZ) := by
    rw [List.map_map]
    rfl
  have h2 : L.toFinset = Finset.univ := Finset.eq_univ_of_forall fun kv => List.mem_toFinset.2 (hall kv)
  rw [h1, ← map_list_prod (Subalgebra.val CZ), ← List.prod_toFinset (ef s) hnd, h2]
  rfl

theorem cen_prod_fix {M : Type} [AddCommGroup M] [Module ℂ M] (cen : ↥CZ →ₐ[ℂ] Module.End ℂ M)
    {ι : Type} (e : ι → ↥CZ) (S : Finset ι) (F : M) (h : ∀ a ∈ S, cen (e a) F = F) :
    cen (∏ a ∈ S, e a) F = F := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, map_one]; rfl
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, map_mul, mul_apply_eq_comp,
      ih fun b hb => h b (Finset.mem_insert_of_mem hb), h a (Finset.mem_insert_self a S)]

theorem cen_prod_ne {M : Type} [AddCommGroup M] [Module ℂ M] (cen : ↥CZ →ₐ[ℂ] Module.End ℂ M)
    {ι : Type} [DecidableEq ι] (e : ι → ↥CZ) (S : Finset ι) (F : M) (hne : cen (∏ a ∈ S, e a) F ≠ 0)
    (a : ι) (ha : a ∈ S) : cen (e a) F ≠ 0 := by
  intro h0
  apply hne
  rw [← Finset.prod_erase_mul S e ha, map_mul, mul_apply_eq_comp, h0, map_zero]

end Series

section Main

theorem lenUnit_natCast_le {D : D7} (i : D.nd.Loc) (n : ℕ) (hn : n ≠ 0) :
    lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {(n : D.nd.O i)}) ≤ (padicValNat (D.nd.l i) n : ℚ) := by
  have := D.nd.lPrime i
  have h := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.addVal_int (O := D.nd.O i) (D.nd.l i) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_not_unit D.nd i) (n : ℤ)
    (by exact_mod_cast hn)
  rw [Int.cast_natCast, padicValInt.of_nat] at h
  rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.lenUnit_span D.nd i h,
    Nat.padicValNat_def]

end Main

end GlobalTheory.CutAtGood

end
