module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppRedW
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharA
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW

variable {D : D7} (X : HidaSetting D)

abbrev wK (kv : Σ k : Fin 2, D.nd.PlG k) : HeightOneSpectrum (𝓞 X.B.I.E) := wB X (D.naut.plGw kv.1 kv.2)

theorem card_wK (kv : Σ k : Fin 2, D.nd.PlG k) :
    Nat.card (𝓞 X.B.I.E ⧸ (wK X kv).asIdeal) = D.host.g kv.1 := by
  rw [card_wB, card_res_host]

theorem card_wc {I : AutInst} (w : HeightOneSpectrum (𝓞 I.E)) :
    Nat.card (𝓞 I.E ⧸ (wc I w).asIdeal) = Nat.card (𝓞 I.E ⧸ w.asIdeal) :=
  Nat.card_congr (Ideal.quotientEquiv (wc I w).asIdeal w.asIdeal (sigO I)
    (Ideal.map_comap_of_surjective _ (sigO I).surjective w.asIdeal).symm).toEquiv

theorem card_wKc (kv : Σ k : Fin 2, D.nd.PlG k) :
    Nat.card (𝓞 X.B.I.E ⧸ (wc X.B.I (wK X kv)).asIdeal) = D.host.g kv.1 := by
  rw [card_wc, card_wK]

theorem mem_wB (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E) :
    a ∈ (wB X w).asIdeal ↔ RingOfIntegers.mapRingEquiv X.ιE a ∈ w.asIdeal := Iff.rfl

theorem gk_mem (kv : Σ k : Fin 2, D.nd.PlG k) : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
  rw [mem_wB, map_natCast]; exact D.naut.plGw_over kv.1 kv.2

theorem gk_mem_c (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wc X.B.I (wK X kv)).asIdeal :=
  natCast_mem_wc X.B.I (gk_mem X kv)

theorem not_both (P : Ideal (𝓞 X.B.I.E)) (hP : P ≠ ⊤) (h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ∈ P)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) ∈ P) : False := by
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
    have h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using h'.map (Int.castRingHom (𝓞 X.B.I.E))
  obtain ⟨a, b, hab⟩ := hcop
  have := P.add_mem (P.mul_mem_left a h0) (P.mul_mem_left b h1)
  rw [hab] at this
  exact hP ((Ideal.eq_top_iff_one _).2 this)

theorem not_both' (P : Ideal (𝓞 X.B.I.E)) (hP : P ≠ ⊤) {k k' : Fin 2} (hk : k ≠ k')
    (h0 : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) (h1 : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ∈ P) : False := by
  fin_cases k <;> fin_cases k'
  · exact hk rfl
  · exact not_both X P hP h0 h1
  · exact not_both X P hP h1 h0
  · exact hk rfl

theorem g_eq_cast : ((X.B.g : ℕ) : 𝓞 X.B.I.E) = ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
  rw [X.g_eq]; push_cast; ring

theorem gk_of_g {P : Ideal (𝓞 X.B.I.E)} (hP : P.IsPrime) (h : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P) :
    ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P := by
  rw [g_eq_cast] at h
  rcases hP.mem_or_mem h with h | h
  exacts [⟨0, h⟩, ⟨1, h⟩]

theorem g_mem_of_gk {P : Ideal (𝓞 X.B.I.E)} {k : Fin 2} (h : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) :
    ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P := by
  rw [g_eq_cast]
  fin_cases k
  · exact P.mul_mem_right _ h
  · exact P.mul_mem_left _ h

theorem over_gk (P : HeightOneSpectrum (𝓞 X.B.I.E)) (k : Fin 2) (hP : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal) :
    ∃ v : D.nd.PlG k, P = wK X ⟨k, v⟩ ∨ P = wc X.B.I (wK X ⟨k, v⟩) := by
  have hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X P).asIdeal := by
    show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    rw [map_natCast]; exact hP
  obtain ⟨v, hv | hv⟩ := cover X k (toH X P) hwH
  · exact ⟨v, Or.inl (by rw [← wB_toH X P, hv])⟩
  · exact ⟨v, Or.inr (by rw [← wB_toH X P, hv, wB_conjH X])⟩

theorem over_g (P : HeightOneSpectrum (𝓞 X.B.I.E)) (hP : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal) :
    ∃ kv : Σ k : Fin 2, D.nd.PlG k, P = wK X kv ∨ P = wc X.B.I (wK X kv) := by
  obtain ⟨k, hk⟩ := gk_of_g X P.isPrime hP
  obtain ⟨v, hv⟩ := over_gk X P k hk
  exact ⟨⟨k, v⟩, hv⟩

theorem wB_inj {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : wB X w = wB X w') : w = w' := by
  refine HeightOneSpectrum.ext ?_
  ext a
  obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv X.ιE).surjective a
  rw [← mem_wB, ← mem_wB, h]

theorem wK_ne {kv kv' : Σ k : Fin 2, D.nd.PlG k} (h : kv ≠ kv') : wK X kv ≠ wK X kv' := by
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  intro he
  by_cases hk : k = k'
  · subst hk
    have hv : v ≠ v' := fun hv => h (by rw [hv])
    exact hv (D.naut.plGw_inj k (wB_inj X he))
  · have h0 := gk_mem X ⟨k, v⟩
    have h1 := gk_mem X ⟨k', v'⟩
    rw [← he] at h1
    exact not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1

theorem wK_ne_wc (kv kv' : Σ k : Fin 2, D.nd.PlG k) : wK X kv ≠ wc X.B.I (wK X kv') := by
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  intro he
  by_cases hk : k = k'
  · subst hk
    rw [show wc X.B.I (wK X ⟨k, v'⟩) = wB X (conjH (D.naut.plGw k v')) from (wB_conjH X _).symm] at he
    have he' := wB_inj X he
    apply D.naut.plGw_nconj k v' v
    have := isConjPl_conjH X (D.naut.plGw k v')
    rw [← he'] at this
    exact this
  · have h0 := gk_mem X ⟨k, v⟩
    have h1 := gk_mem_c X ⟨k', v'⟩
    rw [← he] at h1
    exact not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1

theorem mem_g_of_all {a : 𝓞 X.B.I.E}
    (ha : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → a ∈ P.asIdeal) :
    ∃ c : 𝓞 X.B.I.E, a = ((X.B.g : ℕ) : 𝓞 X.B.I.E) * c := by
  have hk : ∀ k : Fin 2, a ∈ Ideal.span {((D.host.g k : ℕ) : 𝓞 X.B.I.E)} := by
    intro k
    refine mem_span_of_all (D.host.g_prime k) (unram X k) fun P hPm hgP => ?_
    let P' : HeightOneSpectrum (𝓞 X.B.I.E) := ⟨P, hPm.isPrime, fun hb => by
      rw [hb] at hgP
      exact (by exact_mod_cast (D.host.g_prime k).ne_zero : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ≠ 0)
        ((Submodule.mem_bot _).1 hgP)⟩
    exact ha P' (g_mem_of_gk X hgP)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (hk 0)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hk 1)
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
    have h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using h'.map (Int.castRingHom (𝓞 X.B.I.E))
  obtain ⟨α, β, hαβ⟩ := hcop
  refine ⟨α * v + β * u, ?_⟩
  rw [g_eq_cast]
  calc a = (α * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) + β * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)) * a := by rw [hαβ, one_mul]
    _ = α * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) * (v * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)) +
        β * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) * (u * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E)) := by
          rw [hv, hu]; ring
    _ = _ := by ring

theorem exists_eps (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ ε : 𝓞 X.B.I.E, ε - 1 ∈ (wK X kv).asIdeal ∧
      ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 X.B.I.E)) :=
    Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 0) ∪ Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 1)
  have hS : S.Finite := (Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 0)).union
    (Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 1))
  have : Finite S := hS.to_subtype
  have hcop : Pairwise (Function.onFun IsCoprime fun P : S => (P.1).asIdeal) := by
    intro P Q hPQ
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne (P.1).isMaximal (Q.1).isMaximal fun h => hPQ ?_
    exact Subtype.ext (HeightOneSpectrum.ext h)
  obtain ⟨ε, hε⟩ := Ideal.exists_forall_sub_mem_ideal hcop fun P => if P.1 = wK X kv then 1 else 0
  have hmem : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ∈ S := by
    intro P hP
    obtain ⟨k, hk⟩ := gk_of_g X P.isPrime hP
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr hk
  refine ⟨ε, ?_, fun P hP hne => ?_⟩
  · have := hε ⟨wK X kv, hmem _ (g_mem_of_gk X (gk_mem X kv))⟩
    simpa using this
  · have := hε ⟨P, hmem P hP⟩
    simp only [if_neg hne, sub_zero] at this
    exact this

theorem eps_other (kv : Σ k : Fin 2, D.nd.PlG k) {ε : 𝓞 X.B.I.E}
    (hε : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal)
    (k' : Fin 2) (hk : k' ≠ kv.1) : ε ∈ Ideal.span {((D.host.g k' : ℕ) : 𝓞 X.B.I.E)} := by
  refine mem_span_of_all (D.host.g_prime k') (unram X k') fun P hPm hgP => ?_
  let P' : HeightOneSpectrum (𝓞 X.B.I.E) := ⟨P, hPm.isPrime, fun hb => by
    rw [hb] at hgP
    exact (by exact_mod_cast (D.host.g_prime k').ne_zero : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ≠ 0)
      ((Submodule.mem_bot _).1 hgP)⟩
  refine hε P' (g_mem_of_gk X hgP) fun he => ?_
  have h0 := gk_mem X kv
  have h1 : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by rw [← he]; exact hgP
  exact not_both' X _ (wK X kv).isPrime.ne_top hk h1 h0

end Formalism.L2.SG.Pf.KppChar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsGoodRed
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.RowDict Formalism.L2.SG.AllRowsOf
open scoped InnerProductSpace
open MeasureTheory

namespace Formalism.L2.SG.Pf.RowsGoodRed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def VT (t : Tup2 D) : Submodule ℂ (L2X X) :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X ⊓ LinearMap.ker ((ReT X {t} : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def labOf (σ : Fin D.what₂.Drows) : Tup2 D := fun k => D.nd.lab k (D.what₂.ft σ)

def bRow (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (σ : Fin D.what₂.Drows) : L2X X :=
  ((ι (D.sEE (D.what₂.onb σ)) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X)

def LabTie (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : Prop :=
  (∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v)) ∧ (∀ σ, D.ntypes.goodTuple (labOf σ)) ∧
    ∀ σ, bRow X ι σ ∈ VT X (labOf σ)

def ProjT (G : GoodOp X) : Prop :=
  (∀ t : Tup2 D, D.ntypes.goodTuple t → VT X t ≤ goodSub X G) ∧
    ∀ t t' : Tup2 D, t ≠ t' → ∀ φ ∈ VT X t, ∀ φ' ∈ VT X t', ⟪φ, φ'⟫_ℂ = 0

def DcountEq : Prop :=
  ∀ t ∈ labT (D := D), D.ntypes.goodTuple t → dimX X {t} = Module.finrank ℂ (VT X t)

theorem rowsGood_of (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hT : RowDictTie X G ι)
    (hL : LabTie X ι) (hP : ProjT X G) (hD : DcountEq X) : RowsGood X := by
  classical
  obtain ⟨hl1, hl2, hl3⟩ := hL
  refine ⟨hl1, hl2, fun t ht hg => ?_⟩
  have hT' := hT
  obtain ⟨j, hj⟩ := hT
  have hb : ∀ σ, bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := fun σ => by
    have h1 := hj (D.what₂.onb σ)
    simp only at h1
    unfold bRow; rw [h1]; rfl

  have hf : LinearIndependent ℂ (fun σ => ((j (D.what₂.onb σ) : EEC X G) : L2X X)) :=
    (D.what₂.onb.toBasis.linearIndependent.map' j.toLinearEquiv.toLinearMap j.toLinearEquiv.ker).map'
      (EEC X G).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ℂ (bRow X ι) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 : conjL (muX X) (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      rw [← hs]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply, hb σ]
      simp
    have h1 : (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 :=
      (conjL (muX X)).map_eq_zero_iff.1 h0
    have := (linearIndependent_iff'.1 hf) s (fun i => starRingEnd ℂ (g i)) h1 i hi
    simpa using this

  have hspan : ∀ φ ∈ goodSub X G, φ ∈ Submodule.span ℂ (Set.range (bRow X ι)) := by
    intro φ hφ
    obtain ⟨F, hF⟩ := (range_sEE X hT' ⟨φ, hφ.1⟩).1 hφ
    have e : φ = ((ι (D.sEE F) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X) := by rw [hF]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, ← D.what₂.onb.sum_repr F, map_sum, map_sum, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [map_smulₛₗ, map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)

  let Sf : Finset (Fin D.what₂.Drows) := Finset.univ.filter fun σ => labOf σ = t
  have hEq : VT X t = Submodule.span ℂ (Set.range (fun σ : Sf => bRow X ι σ)) := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan φ (hP.1 t hg hφ))
      set φ1 := ∑ σ ∈ Sf, c σ • bRow X ι σ with hφ1
      set φ2 := ∑ σ ∈ Finset.univ.filter (fun σ => ¬ labOf σ = t), c σ • bRow X ι σ with hφ2
      have hsplit : φ = φ1 + φ2 := by
        rw [← hc, hφ1, hφ2, Finset.sum_filter_add_sum_filter_not]
      have h1V : φ1 ∈ VT X t := Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (by
        have := hl3 σ; rwa [(Finset.mem_filter.1 hσ).2] at this)
      have h2V : φ2 ∈ VT X t := by
        have := Submodule.sub_mem _ hφ h1V
        rwa [hsplit, add_sub_cancel_left] at this
      have horth : ⟪φ2, φ2⟫_ℂ = 0 := by
        conv_lhs => rw [hφ2]
        rw [sum_inner]
        refine Finset.sum_eq_zero fun σ hσ => ?_
        rw [inner_smul_left, hP.2 (labOf σ) t (Finset.mem_filter.1 hσ).2 _ (hl3 σ) _ h2V, mul_zero]
      have h20 : φ2 = 0 := inner_self_eq_zero.1 horth
      rw [hsplit, h20, add_zero, hφ1]
      exact Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, hσ⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨σ, rfl⟩
      have := hl3 σ
      rwa [(Finset.mem_filter.1 σ.2).2] at this
  have hli' : LinearIndependent ℂ (fun σ : Sf => bRow X ι σ) := hli.comp (Subtype.val : Sf → _) Subtype.val_injective
  rw [hD t ht hg, hEq, finrank_span_eq_card hli', Fintype.card_coe]
  rfl

def EtConv : Prop := ∀ (S S' : Set (Tup2 D)) (φ : L2X X), ReT X S (ReT X S' φ) = ReT X (S ∩ S') φ

def EtEmpty : Prop := ∀ φ : L2X X, ReT X ∅ φ = 0

def EtAdj : Prop := ∀ (S : Set (Tup2 D)) (φ ψ : L2X X), ⟪ReT X S φ, ψ⟫_ℂ = ⟪φ, ReT X S ψ⟫_ℂ

def EtGood (G : GoodOp X) : Prop :=
  ∀ t : Tup2 D, D.ntypes.goodTuple t → ∀ φ : L2X X, G.Rg (ReT X {t} φ) = ReT X {t} φ

theorem mem_VT {t : Tup2 D} {φ : L2X X} (h : φ ∈ VT X t) : ReT X {t} φ = φ := by
  have h2 := (Submodule.mem_inf.mp h).2
  rw [LinearMap.mem_ker] at h2
  simpa [sub_eq_zero] using h2

theorem projT_of (G : GoodOp X) (hC : EtConv X) (hE : EtEmpty X) (hA : EtAdj X) (hG : EtGood X G) : ProjT X G := by
  refine ⟨fun t ht φ hφ => ?_, fun t t' htt φ hφ φ' hφ' => ?_⟩
  · refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hφ).1, ?_⟩
    have h1 := hG t ht φ
    rw [mem_VT X hφ] at h1
    rw [LinearMap.mem_ker]
    simpa [sub_eq_zero] using h1
  · rw [← mem_VT X hφ, ← mem_VT X hφ', hA, hC]
    have hE0 : ({t} : Set (Tup2 D)) ∩ {t'} = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      exact htt
    rw [hE0, hE, inner_zero_right]

theorem etEmpty : EtEmpty X := by
  intro φ
  have hES : ∀ g, (ES (D := D) ∅).coeff g = 0 := by
    intro g
    simp [ES]
  have hg : egA X (ES (D := D) ∅) = 0 := by
    funext y
    simp [egA, hES]
  have he : eT X ∅ = 0 := by
    funext x
    simp [eT, Formalism.MainNotions.S.AutInst.convF, hg]
  unfold ReT
  split_ifs with h
  · have hT := (Classical.choose_spec h).2
    have h0 : ∀ x, ⟪x, (Classical.choose h) φ⟫_ℂ = 0 := fun x => by
      rw [hT x φ, he]
      simp
    exact inner_self_eq_zero.mp (h0 _)
  · rfl

theorem invInvariant_muf : X.B.μf.IsInvInvariant := by
  have : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have he1 : X.B.e 1 ≠ 0 := by
    rw [X.e_eq]
    have h1 : (1 : X.B.I.Gf) ∈ X.K2 := hK.1
    rw [ite_eq_left (show (1 : X.B.I.Gf) ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw from h1)]
    have hc : X.chi2 1 ≠ 0 := by
      intro h0; have := hK.2.2.2.2 1 h1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hv : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (ENNReal.toReal_pos hL.2.2.1.ne' hL.2.2.2.ne).ne'
    exact div_ne_zero (star_ne_zero.2 hc) hv
  exact Formalism.MainNotions.BridgeLemma.inv_invariant_of_bi_invariant X.B.μf (fun g => ‖X.B.e g‖) X.B.e_adm.1.continuous.norm
    X.B.Re_spec.1.norm (norm_pos_iff.2 he1)

def EtSA : Prop := ∀ (S : Set (Tup2 D)) (x : X.B.I.Gf), star (eT X S x⁻¹) = eT X S x

theorem etAdj_of (hSA : EtSA X) : EtAdj X := by
  have := invInvariant_muf X
  intro S φ ψ
  have hT := reT_spec X (etInt_holds X) S
  have := X.B.sf
  have := X.B.haar
  obtain ⟨hmul, hone, hiso⟩ := Formalism.L2.SG.Pf.reg_alg
    Formalism.L2.SG.Closed.UnimodGf_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec
  have hreg : ∀ g : X.B.I.Gf, ⟪X.B.R ((1, g) : X.B.I.GA) φ, ψ⟫_ℂ = ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ := by
    intro g
    have h := Formalism.L2.SG.Pf.inner_orbit X.B.R hmul hiso ((1, g) : X.B.I.GA) 1 φ ψ
    simpa only [hone, one_apply_eq_self, mul_one, Prod.inv_mk, inv_one] using h
  calc ⟪ReT X S φ, ψ⟫_ℂ = star ⟪ψ, ReT X S φ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = star (∫ g, eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ ∂X.B.μf) := by rw [hT.2]
    _ = ∫ g, star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← starRingEnd_apply, ← integral_conj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (starRingEnd ℂ) (eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ) = _
        rw [map_mul]
        show _ = star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ
        rw [← hreg g, inner_conj_symm]
        rfl
    _ = ∫ g, star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← MeasureTheory.integral_inv_eq_self (fun g => star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ) X.B.μf]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g⁻¹⁻¹) : X.B.I.GA) ψ⟫_ℂ = _
        rw [inv_inv]
    _ = ∫ g, eT X S g * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * _ = _
        rw [hSA S g]
    _ = ⟪φ, ReT X S ψ⟫_ℂ := (hT.2 φ ψ).symm

theorem etGood_of (G : GoodOp X)
    (hEC : ∀ S S' : Set (Tup2 D), X.B.I.convF X.B.μf (egA X (ES S')) (eT X S) = eT X (S' ∩ S)) : EtGood X G := by
  intro t ht φ
  have h1 := Formalism.L2.SG.Pf.AllRowsRMul.isRConvF_conv X G.Rg_spec (reT_spec X (etInt_holds X) {t})
  have e : X.B.I.convF X.B.μf (eg X) (eT X {t}) = eT X {t} := by
    rw [← goodIdempotent_eq, ← ES_good, hEC]
    congr 1
    exact Set.inter_eq_right.2 (Set.singleton_subset_iff.2 ht)
  rw [e] at h1
  have h2 := isRConvF_unique X h1 (reT_spec X (etInt_holds X) {t})
  exact congrArg (fun T : L2X X →L[ℂ] L2X X => T φ) h2

end Formalism.L2.SG.Pf.RowsGoodRed
end
end

