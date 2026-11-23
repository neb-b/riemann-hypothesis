module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.Detection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.Choice
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem detects_mono {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x)
    {S T : Set F.G₀} (hST : S ⊆ T) (h : Detects k S) : Detects k T :=
  fun z hz hT => h z hz fun σ hσ => hT σ (hST hσ)

theorem UpperTheory.V.Pa.choice :
    UpperTheory.V.Pa.Choice := by
  intro l _ F n h x hl hphi hε hN3
  classical
  set S : Set F.G₀ := {σ | σ ∈ F.G' ∧ ∀ i : Fin (h + 1),
    (Polynomial.map (algebraMap (x i).A (FractionRing (x i).A)) ((mat (x i).ρ) σ).charpoly).Separable} with hS
  have hcl : (F.G' : Set F.G₀) ⊆ closure S := Det.omDense x hN3
  have hSG : S ⊆ F.G' := fun σ hσ => hσ.1
  have k0 : ∀ i, Kap (x i) := fun i => (Det.kapEx (x i) hphi).some
  have hdet : ∀ i, Detects (k0 i) S := fun i => detection l F n (x i) (k0 i) hl hε S hSG hcl
  choose Tf hTS hTd using fun i => Det.detFin (k0 i) S hphi (hdet i)
  set U : Finset F.G₀ := Finset.univ.biUnion Tf with hU
  let sg : Fin U.card → F.G₀ := fun a => (U.equivFin.symm a : F.G₀)
  have hsgU : ∀ a, sg a ∈ U := fun a => (U.equivFin.symm a).2
  have hsgS : ∀ a, sg a ∈ S := fun a => by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (hsgU a)
    exact hTS i hi
  have hTr : ∀ i, (Tf i : Set F.G₀) ⊆ Set.range sg := fun i y hy => by
    have hyU : y ∈ U := Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hy⟩
    exact ⟨U.equivFin ⟨y, hyU⟩, by simp [sg]⟩
  have hdr : ∀ i, Detects (k0 i) (Set.range sg) := fun i => detects_mono (k0 i) (hTr i) (hTd i)
  choose d hd0 hd using fun i => Det.onePt (k0 i) sg (fun a => (hsgS a).2 i) (hdr i)
  have hD0 : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)
  choose x' j k' al hext hcard hdet' hal using
    fun i => hd i (∏ i, d i) (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) hD0
  exact ⟨U.card, sg, x', j, k', al, fun a => (hsgS a).1, hext, fun i => by rw [hcard, hcard],
    hdet', fun i a => hal i a⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.S6
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem s6 : S6 := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ rF hl hc hr hk
  letI : Algebra Bh (FractionRing x.A) := rF.toAlgebra
  have hk' : RingHom.ker (algebraMap Bh (FractionRing x.A)) = maximalIdeal Bh := hk
  obtain ⟨H⟩ := hat_ex P (Bh := Bh) hr
  have hs := rF_surj P (Bh := Bh) hr hk'
  haveI := hc.noeth
  haveI := hc.complete
  haveI := H.fin
  have h2 : IsUnit (2 : Bh) := by
    by_contra hn
    have h3 : (2 : Bh) ∈ RingHom.ker (algebraMap Bh (FractionRing x.A)) := by rw [hk']; exact hn
    rw [RingHom.mem_ker, map_ofNat] at h3
    have h4 : (2 : x.K) = 0 := by
      have h5 : (algebraMap x.A (FractionRing x.A)).comp (PowerSeries.C (R := x.K)) 2 = 0 := by rw [map_ofNat]; exact h3
      exact (map_eq_zero _).1 h5
    have h6 : IsUnit (2 : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hl ?_)
      have h7 : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by simpa using hlt
      rw [PadicInt.norm_int_lt_one_iff_dvd] at h7
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 (by exact_mod_cast h7)
    have h8 := h6.map (algebraMap ℤ_[l] x.K)
    rw [map_ofNat, h4] at h8
    exact not_isUnit_zero h8
  have hst := hat_st P hr H
  have hrg := hat_range P hs H
  obtain ⟨U, hx, hrk⟩ := idem x.a H.DE H.T H.r x.a_pos x.a_le h2 H.ch H.tr hk' (hat_chi P hr H) hst
    fun Z hZ => (hrg Z).1 hZ
  have hg : Nonempty (GrAlg H.T n x.a H.r U.ep) := by
    rcases x.a_le.lt_or_eq with ha | ha
    · exact gr_E x.a H.T H.r U x.a_pos ha hk' hst hx fun y => (hrg _).2 ⟨y, rfl⟩
    · have hn : 1 ≤ n := ha ▸ x.a_pos
      revert U
      rw [ha]
      intro U hx _
      exact gr_I H.T H.r U hn hst hx
  obtain ⟨g⟩ := hg
  exact urep_of H g U.coi hrk

end UpperTheory.V.Pa
end

