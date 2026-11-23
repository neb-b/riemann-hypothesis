module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.BlockCount
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

theorem UpperTheory.Gal.TypesAndIwahori.blockCount :
    UpperTheory.Gal.TypesAndIwahori.BlockCount := by
  intro β N s d hd θ
  have hsum : Multiset.map (fun i => θ (blockOf d hd i)) Finset.univ.val =
      ∑ i, ({θ (blockOf d hd i)} : Multiset β) := by
    rw [← Multiset.sum_map_singleton (Multiset.map _ _), Multiset.map_map]
    rfl
  rw [hsum, ← (stdBlocks d hd).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [blockOf, Multiset.nsmul_singleton]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.GrpFacts
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

private theorem unitRes_surj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Function.Surjective (unitRes k) := by
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ IsLocalRing.residue_surjective inferInstance

theorem UpperTheory.Gal.TypesAndIwahori.grpFacts :
    UpperTheory.Gal.TypesAndIwahori.GrpFacts := by
  intro k _ _ _ _ s θ μ hθ hμ a b hab
  have key : (∀ u, θ a (unitRes k u) = θ b (unitRes k u)) → False := by
    intro h
    apply hab
    apply hθ
    refine MonoidHom.ext fun w => ?_
    obtain ⟨u, rfl⟩ := unitRes_surj k w
    exact h u
  have hres : ∀ c u, UpperTheory.TNZ.res (μ c) u = θ c (unitRes k u) := fun c u => hμ c u
  have hdiv : ∀ u, UpperTheory.TNZ.res (μ a / μ b) u = θ a (unitRes k u) / θ b (unitRes k u) := by
    intro u
    show (μ a / μ b) (unitIncl k u) = _
    rw [MonoidHom.div_apply, hμ a u, hμ b u]
  refine ⟨fun h => key fun u => ?_, ?_⟩
  · rw [← hres, ← hres, h]
  · unfold UpperTheory.TNZ.cc UpperTheory.TNZ.cond
    set S := {c : ℕ | ∀ u : (𝒪[k])ˣ, (u : 𝒪[k]) - 1 ∈ 𝓂[k] ^ c → UpperTheory.TNZ.res (μ a / μ b) u = 1} with hS
    have h1 : 1 ∈ S := by
      intro u hu
      rw [pow_one] at hu
      have hr : unitRes k u = 1 := by
        ext
        simp only [unitRes, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
        have hz : IsLocalRing.residue 𝒪[k] ((u : 𝒪[k]) - 1) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hu
        rw [map_sub, map_one, sub_eq_zero] at hz
        exact hz
      rw [hdiv, hr, map_one, map_one, div_one]
    have h0 : 0 ∉ S := by
      intro h
      apply key
      intro u
      have := h u (by simp)
      rw [hdiv, div_eq_one] at this
      exact this
    apply le_antisymm (Nat.sInf_le h1)
    rw [Nat.one_le_iff_ne_zero]
    intro hz
    rcases Nat.sInf_eq_zero.1 hz with h | h
    · exact h0 h
    · rw [h] at h1
      exact h1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.IndSupp
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

theorem UpperTheory.Gal.TypesAndIwahori.indSupp :
    UpperTheory.Gal.TypesAndIwahori.IndSupp := by
  intro G W _ _ _ _ _ P C σ u hC hu
  classical
  let φ : G → W := fun g => if h : ∃ p : P, ∃ c ∈ C, g = ↑p * c then σ h.choose u else 0
  have key : ∀ (p : P) (c : G), c ∈ C → φ (↑p * c) = σ p u := by
    intro p c hc
    have h : ∃ p' : P, ∃ c' ∈ C, (↑p * c : G) = ↑p' * c' := ⟨p, c, hc, rfl⟩
    simp only [φ, dif_pos h]
    obtain ⟨c', hc', hpc⟩ := h.choose_spec
    have hq : ((h.choose⁻¹ * p : P) : G) ∈ C := by
      have e : ((h.choose⁻¹ * p : P) : G) = c' * c⁻¹ := by
        push_cast
        rw [eq_mul_inv_iff_mul_eq, mul_assoc]
        exact (congrArg _ hpc).trans (inv_mul_cancel_left _ _)
      rw [e]
      exact C.mul_mem hc' (C.inv_mem hc)
    have hfix := hu _ hq
    calc σ h.choose u = σ h.choose (σ (h.choose⁻¹ * p) u) := by rw [hfix]
      _ = σ p u := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have zero : ∀ g : G, (¬∃ p : P, ∃ c ∈ C, g = ↑p * c) → φ g = 0 := by
    intro g hg
    simp only [φ, dif_neg hg]
  have memInd : φ ∈ indSpace P σ := by
    show ∀ (h : P) (g : G), φ (↑h * g) = σ h (φ g)
    intro h g
    by_cases hg : ∃ p : P, ∃ c ∈ C, g = ↑p * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [← mul_assoc, ← Subgroup.coe_mul, key _ _ hc, key _ _ hc, map_mul, Module.End.mul_apply]
    · have hhg : ¬∃ p : P, ∃ c ∈ C, ↑h * g = ↑p * c := by
        rintro ⟨p, c, hc, hpc⟩
        exact hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← hpc, Subgroup.coe_inv, inv_mul_cancel_left]⟩
      rw [zero _ hg, zero _ hhg, map_zero]
  have smooth : (⟨φ, memInd⟩ : indSpace P σ) ∈ smoothPart (ind P σ) := by
    apply mem_smoothPart_of_nhds
    refine Filter.mem_of_superset (hC.mem_nhds C.one_mem) ?_
    intro c hc
    show (ind P σ c) ⟨φ, memInd⟩ = ⟨φ, memInd⟩
    apply Subtype.ext
    funext x
    show φ (x * c) = φ x
    by_cases hx : ∃ p : P, ∃ c' ∈ C, x = ↑p * c'
    · obtain ⟨p, c', hc', rfl⟩ := hx
      rw [mul_assoc, key _ _ (C.mul_mem hc' hc), key _ _ hc']
    · have hxc : ¬∃ p : P, ∃ c' ∈ C, x * c = ↑p * c' := by
        rintro ⟨p, c', hc', hpc⟩
        exact hx ⟨p, c' * c⁻¹, C.mul_mem hc' (C.inv_mem hc), by rw [← mul_assoc, ← hpc, mul_inv_cancel_right]⟩
      rw [zero _ hx, zero _ hxc]
  exact ⟨⟨⟨φ, memInd⟩, smooth⟩, fun p c hc => key p c hc, fun g hg => zero g hg⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.ParaFactor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

theorem paraFactor : ParaFactor := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e
  constructor
  · intro g
    obtain ⟨x, hx⟩ := redLevi_surjective (k := k) (m := m) (parahoricProj k e g)
    have hq := leviEmb_mem_parahoric (k := k) e x
    have hqp := parahoricProj_leviEmb (k := k) e x
    set q : parahoric k e := ⟨leviEmb k e (x : Levi k m), hq⟩ with hqdef
    have hr : ((q⁻¹ * g : parahoric k e) : GL n k) ∈ proRad k e := by
      rw [← parahoricProj_eq_one_iff, map_mul, map_inv, hqp, hx, inv_mul_cancel]
    obtain ⟨u, hu, c, hc, hrc⟩ := IwahoriFactor.exists_jPlus_mul_KOne e hr
    have huR : u ∈ unipRad k e := hu.1
    have huP : u ∈ parab k e := unipRad_le_parab k e huR
    have hqP : (q : GL n k) ∈ parab k e := leviEmb_mem_parab k e _
    refine ⟨⟨(q : GL n k) * u, mul_mem hqP huP⟩, x, ?_, ?_, hx, c, hc, ?_⟩
    · exact mul_mem (leviEmb_mem_KO e x.2) hu.2
    · have hsplit : (⟨(q : GL n k) * u, mul_mem hqP huP⟩ : parab k e) = ⟨q, hqP⟩ * ⟨u, huP⟩ := rfl
      rw [hsplit, map_mul, (coe_mem_unipRad k ⟨u, huP⟩).1 huR, mul_one]
      exact leviProj_leviEmb k e _
    · have h2 : (g : GL n k) = (q : GL n k) * ((q⁻¹ * g : parahoric k e) : GL n k) := by
        simp
      rw [h2, hrc, mul_assoc]
  · intro p hp
    obtain ⟨d, hd, u, hu, hpdu⟩ := IwahoriFactor.exists_jLevi_mul_jPlus e p.2 hp
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hd
    have huR : u ∈ unipRad k e := hu.1
    have huP : u ∈ parab k e := unipRad_le_parab k e huR
    have hdP : leviEmb k e y ∈ parab k e := leviEmb_mem_parab k e y
    have hsplit : p = ⟨leviEmb k e y, hdP⟩ * ⟨u, huP⟩ := Subtype.ext hpdu
    rw [hsplit, map_mul, (coe_mem_unipRad k ⟨u, huP⟩).1 huR, mul_one, leviProj_leviEmb]
    exact hy

end UpperTheory.Gal.TypesAndIwahori
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TypeToIw
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

private theorem typeToIw_key (hF : UpperTheory.Gal.TypesAndIwahori.FinTri) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N s : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) {g : GL (Fin N) k}
    (hg : g ∈ KO k (Fin N)) (hlow : ∀ i j, j < i → valuation k ((g : Matrix (Fin N) (Fin N) k) i j) < 1) :
    ∃ hpar : g ∈ parahoric k (stdBlocks d hd), ∀ a,
      ((GeneralLinearGroup.det (parahoricProj k (stdBlocks d hd) ⟨g, hpar⟩ a) : 𝓀[k]ˣ) : 𝓀[k]) =
        ∏ j : Fin (d a), (redK k (Fin N) ⟨g, hg⟩ : Matrix (Fin N) (Fin N) 𝓀[k])
          (stdBlocks d hd ⟨a, j⟩) (stdBlocks d hd ⟨a, j⟩) := by
  obtain ⟨hp, hdet⟩ := hF 𝓀[k] N s d hd (redK k (Fin N) ⟨g, hg⟩) (fun i j hij => by
    rw [redK_eq_zero_iff]
    exact hlow i j hij)
  refine ⟨mem_levelPre.2 ⟨hg, hp⟩, fun a => ?_⟩
  exact hdet a

theorem UpperTheory.Gal.TypesAndIwahori.typeToIw :
    UpperTheory.Gal.TypesAndIwahori.FinTri → UpperTheory.Gal.TypesAndIwahori.TypeToIw := by
  intro hF k _ _ _ _ N s d hd V _ _ π θ μ hμ v hv
  rw [mem_typeSp] at hv
  constructor
  · intro h hK hlow hdiag
    obtain ⟨hpar, hdet⟩ := typeToIw_key hF d hd hK hlow
    have hv' := hv ⟨h, hpar⟩
    have hone : ∀ a, GeneralLinearGroup.det (parahoricProj k (stdBlocks d hd) ⟨h, hpar⟩ a) = 1 := by
      intro a
      ext
      rw [hdet a, Units.val_one]
      apply Finset.prod_eq_one
      intro j _
      have hx := (redK_eq_iff (k := k) ⟨h, hK⟩ (stdBlocks d hd ⟨a, j⟩) (stdBlocks d hd ⟨a, j⟩) 1).2 (by
        simpa using hdiag (stdBlocks d hd ⟨a, j⟩))
      simpa using hx
    rw [typeChar_apply] at hv'
    simpa [hone] using hv'
  · intro t ht
    have hI := mem_iwahori.1 (diagT_mem_iwahori (k := k) ht)
    obtain ⟨hpar, hdet⟩ := typeToIw_key hF d hd hI.1 hI.2
    have hv' := hv ⟨_, hpar⟩
    rw [typeChar_apply] at hv'
    refine hv'.trans ?_
    congr 2
    have hu : ∀ i, ∃ u, unitIncl k u = t i := fun i => valuation_eq_one_iff.1 (ht i)
    choose u hu using hu
    have hdetu : ∀ a, GeneralLinearGroup.det (parahoricProj k (stdBlocks d hd) ⟨_, hpar⟩ a) =
        ∏ j : Fin (d a), unitRes k (u (stdBlocks d hd ⟨a, j⟩)) := by
      intro a
      ext
      rw [hdet a, Units.coe_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hx := (redK_eq_iff (k := k) ⟨_, hI.1⟩ (stdBlocks d hd ⟨a, j⟩) (stdBlocks d hd ⟨a, j⟩)
        (u (stdBlocks d hd ⟨a, j⟩) : 𝒪[k])).2 (by
          have h1 := congrArg Units.val (hu (stdBlocks d hd ⟨a, j⟩))
          simp only [val_diagT, diagonal_apply_eq]
          rw [← h1]
          simp only [unitIncl, Units.coe_map, MonoidHom.coe_coe]
          refine lt_of_eq_of_lt (congrArg (valuation k) (sub_eq_zero.2 rfl)) ?_
          simp)
      rw [hx]
      simp
    rw [torusChar_apply]
    simp_rw [hdetu, map_prod]
    rw [← (stdBlocks d hd).prod_comp, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun j _ => ?_
    have hb : blockOf d hd (stdBlocks d hd ⟨a, j⟩) = a := by simp [blockOf]
    rw [hb, ← hu]
    exact (hμ a _).symm
end

