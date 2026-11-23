module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.VanPairs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.PolySupp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecAlg

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.RelIndexNeZeroOfOpen
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw mat sim)
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.W2.Seed (Arith Setup Cong1 apart_of_not_mem pKNOpen pKNIdx pKNIff pLatCoord pRepLaws)
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.Int.Geo.Pl (Frame)
open GlobalTheory.LFun (KGL)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
variable {x : E} {U : Submodule ℂ (UA E n → ℂ)} {w₀ : Plc E} {Up : Plc E → Prop}

private theorem th_eq (F : Frame S) (g : GUf E n) : F.th g = CertificateRingHomMap.th g :=
  Subtype.ext (Prod.ext (Units.ext (F.th_mat g)) (F.th_sim g))

private theorem continuous_th : Continuous (CertificateRingHomMap.th : GUf E n → GUf E n) := by
  refine continuous_induced_rng.2 ?_
  exact ((GlobalTheory.SplitPts.continuous_invT _).comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_inv.comp (continuous_snd.comp continuous_subtype_val))

private theorem relIndex_ne_zero_of_open {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    {K O : Subgroup X} (hK : IsCompact (K : Set X)) (hO : IsOpen (O : Set X)) : O.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((O.subgroupOf K : Subgroup K) : Set K) := hO.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

private theorem isCompact_comap_th (F : Frame S) {K : Subgroup (GUf E n)} (hK : IsCompact (K : Set (GUf E n))) :
    IsCompact ((K.comap F.th : Subgroup (GUf E n)) : Set (GUf E n)) := by
  have hImage : (K.comap F.th : Set (GUf E n)) = CertificateRingHomMap.th '' (K : Set (GUf E n)) := by
    ext g
    constructor
    · intro h
      exact ⟨F.th g, h, by rw [th_eq F, CertificateRingHomMap.th_th]⟩
    · rintro ⟨y, hy, rfl⟩
      change F.th (CertificateRingHomMap.th y) ∈ K
      rwa [th_eq F, CertificateRingHomMap.th_th]
  rw [hImage]
  exact hK.image continuous_th

private theorem relIdx (F : Frame S) {K : Subgroup (GUf E n)} (hK : IsCompact (K : Set (GUf E n))) (N : ℕ) (hN : 0 < N) :
    (S.L.KN N).relIndex ((K.comap F.th).map F.j) ≠ 0 := by
  rw [← Subgroup.relIndex_comap]
  have hO := pKNOpen (pKNIff (pLatCoord pRepLaws)) E A n p S F.tr N hN
  rw [← F.j_tr] at hO
  exact relIndex_ne_zero_of_open (isCompact_comap_th F hK) hO

private theorem cong_at (F : Frame S) (k : GUf E n) (N : ℕ) (hN : 0 < N) (hk : S.L.CongOne N (F.j k)) (w : Plc E)
    (hp : (p : 𝓞 E) ∉ w.asIdeal) : Cong1 N w (F.a w * comp w k * (F.a w)⁻¹) := by
  have hk' : S.L.CongOne N (F.tr.j k) := by simpa only [← F.j_tr] using hk
  have h := ((pKNIff (pLatCoord pRepLaws)) E A n p S F.tr k).2 N hN
  simpa only [map_mul, map_inv, ← F.a_tr w, CertificateRingHomMap.comp, MonoidHom.comp_apply]
    using h.mp hk' w hp

private theorem val_nat_lt_one {w : Plc E} {r N : ℕ} (hr : (r : 𝓞 E) ∈ w.asIdeal) (hN : r ∣ N) :
    Valued.v (N : w.adicCompletion E) < 1 := by
  have h1 : (N : 𝓞 E) ∈ w.asIdeal := by
    obtain ⟨c, rfl⟩ := hN
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hr
  have h2 := (w.valuation_lt_one_iff_mem (K := E) (N : 𝓞 E)).2 h1
  have e : (N : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E (N : 𝓞 E)) := by
    rw [map_natCast, map_natCast]
  rw [e]
  exact (w.valuedAdicCompletion_eq_valuation' _).trans_lt h2

private theorem mul_lt_left {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) < 1) (i j : Fin n) : Valued.v ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_mul' (hA _ _) le_rfl) (by simpa using hB l j)

private theorem mul_lt_right {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, Valued.v (A i j) < 1) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin n) : Valued.v ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_mul' le_rfl (hB _ _)) (by simpa using hA i l)

private theorem sub_lt_of_conj {w : Plc E} (a g : GLw n w) (ha : a ∈ KGL w (n := n))
    (h : ∀ i k, Valued.v (((a * g * a⁻¹).val - 1) i k) < 1) (i k : Fin n) : Valued.v ((g.val - 1) i k) < 1 := by
  have hK := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n a).2).1 ha
  have e : g.val - 1 = (a⁻¹).val * ((a * g * a⁻¹).val - 1) * a.val := by
    have h1 : (a⁻¹).val * a.val = 1 := by simp
    have h2 : (a⁻¹).val * (a * g * a⁻¹).val * a.val = g.val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mul_sub, Matrix.sub_mul, h2, Matrix.mul_one, h1]
  rw [e]
  exact mul_lt_right (mul_lt_left hK.2 h) hK.1 i k

private theorem le_one_of_sub_lt {w : Plc E} {g : GLw n w} (h : ∀ i k, Valued.v ((g.val - 1) i k) < 1) (i k : Fin n) :
    Valued.v (g.val i k) ≤ 1 := by
  have e : g.val i k = (g.val - 1) i k + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i k := by simp
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le (h i k).le ?_)
  by_cases hik : i = k <;> simp [hik, Matrix.one_apply]

private theorem iw_of_cong {w : Plc E} (a g : GLw n w) (ha : a ∈ KGL w (n := n))
    (h : ∀ i k, Valued.v (((a * g * a⁻¹).val - 1) i k) < 1)
    (h' : ∀ i k, Valued.v (((a * g⁻¹ * a⁻¹).val - 1) i k) < 1) : g ∈ Iw n w := by
  have c1 := sub_lt_of_conj a g ha h
  have c2 := sub_lt_of_conj a g⁻¹ ha h'
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1).2 ⟨le_one_of_sub_lt c1, le_one_of_sub_lt c2, fun i j hij => ?_⟩
  have e : g.val i j = (g.val - 1) i j := by
    simp [Matrix.one_apply, (ne_of_lt hij).symm]
  rw [e]
  exact c1 i j

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.tyEx :
    UpperTheory.Gal.Spc.TyEx := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hOff r W hAux N hrN hSt
  have hS0 : w₀ ∈ V.S := V.shape.mem
  have hw : IsSplitAt w₀ ∧ (p : 𝓞 E) ∉ w₀.asIdeal := ⟨V.split, hOff.1 w₀ hS0⟩
  have hN : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  haveI : Fact r.Prime := ⟨hAux.prime⟩
  choose L hL using fun w : Spl E p => facEx E A n p S F w
  have hcomp : ∀ (u : Plc E) (g : GUf E n), comp u (F.th g) = invT n _ (comp u g) := fun u g => by
    rw [th_eq, UpperTheory.Gal.CertificateRingHomMap.comp_th]
  let K : Subgroup S.G.GAf := ((lev V.S V.Kw).comap F.th).map F.j ⊓ ⨅ w ∈ W, (Iw n w.1).comap (L w).pr
  have hK : ∀ k, k ∈ K ↔ (∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw) ∧ ∀ w ∈ W, (L w).pr k ∈ Iw n w.1 := by
    intro k
    simp only [K, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_iInf, Subgroup.mem_comap]
    exact and_congr_left' (exists_congr fun _ => and_comm)
  obtain ⟨-, hap, -, -, hcc, -⟩ := UpperTheory.Gal.CertificateRingHomMap.pLocComm_of E n w₀ hw.1
  have hfact : (L ⟨w₀, hw⟩).Fact K (V.J.comap (invT n _)) := by
    refine ⟨fun y hy => (hK _).2 ⟨⟨CertificateRingHomMap.loc hw.1 y, ((hL ⟨w₀, hw⟩).2 y).symm, ?_⟩, fun w hW => ?_⟩, fun g hg => ?_⟩
    · refine UpperTheory.Gal.CertificateRingHomMap.mem_lev.2 ⟨?_, fun u hu => ?_, fun u hu hu' => ?_⟩
      · rw [F.th_sim, UpperTheory.Gal.CertificateRingHomMap.sim_loc, inv_one]
        exact one_mem _
      · rw [hcomp]
        by_cases h1 : u = w₀
        · subst h1
          rw [UpperTheory.Gal.CertificateRingHomMap.comp_loc, V.Kw0]
          exact hy
        · have h2 : u ≠ cj w₀ := fun h => (V.shape.up w₀ hS0 V.split).2 (h ▸ hu)
          rw [UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw.1 ((hap u).2 ⟨h1, h2⟩), map_one]
          exact one_mem _
      · have h1 : u ≠ w₀ := fun h => hu (h ▸ hS0)
        have h2 : u ≠ cj w₀ := fun h => hu' (by rw [h, hcc]; exact hS0)
        rw [hcomp, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw.1 ((hap u).2 ⟨h1, h2⟩), map_one]
        exact one_mem _
    · have e : (L ⟨w₀, hw⟩).loc y = F.j (CertificateRingHomMap.loc hw.1 y) := (hL ⟨w₀, hw⟩).2 y
      rw [e, (hL w).1, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw.1 (apart_of_not_mem (hAux.off w₀ hS0) (hAux.half.above w hW))]
      exact one_mem _
    · obtain ⟨⟨k', rfl, hk'⟩, -⟩ := (hK g).1 hg
      have e : (L ⟨w₀, hw⟩).pr (F.j k') = comp w₀ k' := (hL ⟨w₀, hw⟩).1 k'
      have h := (UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 hk').2.1 w₀ hS0
      rw [hcomp, V.Kw0] at h
      rw [e]
      exact h
  have hle : S.L.KN N.1 ≤ K := by
    intro k hk
    obtain ⟨k', rfl, hk', -⟩ := hSt k hk
    refine (hK _).2 ⟨⟨k', rfl, hk'⟩, fun w hW => ?_⟩
    have hr := hAux.half.above w hW
    have hv := val_nat_lt_one hr hrN
    rw [(hL w).1]
    refine iw_of_cong (F.a w.1) _ (F.a_int w.1 r hAux.prime hAux.good hr) (fun i k => ?_) (fun i k => ?_)
    · exact (cong_at F k' N.1 hN hk.1 w.1 w.2.2 i k).trans_lt hv
    · have h := cong_at F k'⁻¹ N.1 hN (by rw [map_inv]; exact hk.2) w.1 w.2.2 i k
      rw [map_inv] at h
      exact h.trans_lt hv
  refine ⟨L, hw,
    { L := L ⟨w₀, hw⟩
      K := K
      K₀ := S.L.KN N.1
      J := V.J.comap (invT n _)
      ψ := V.χ.comp ((invT n _).subgroupComap V.J)
      fact := hfact
      le := hle
      ker := fun k hk h => ?_
      idx := fun h0 => relIdx F V.cpt N.1 hN (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
      cms := (pKNIdx (pKNOpen (pKNIff (pLatCoord pRepLaws))) E A n p S F.tr N.1 hN).1 },
    ⟨hL, rfl, rfl, hK, fun y y' h => ?_, fun y y' h => ?_⟩⟩
  · obtain ⟨k', rfl, -, hJ, hχ⟩ := hSt k hk
    rw [← hχ]
    refine congrArg V.χ (Subtype.ext ?_)
    show invT n _ ((L ⟨w₀, hw⟩).pr (F.j k')) = comp w₀ (F.th k')
    rw [hcomp]
    exact congrArg _ ((hL ⟨w₀, hw⟩).1 k')
  · have e : y' = invT n _ y := Units.ext h
    rw [e]
    rfl
  · exact congrArg V.χ (Subtype.ext (Units.ext h.symm))
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecOfF
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.CertificateRingHomMap (wop wmul)
open UpperTheory.Gal.LocalSmoothExtension
open Formalism.UG (Hecke)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Abstract

variable {H : Type} [Group H] {K : Subgroup H} {M : Type} [AddCommGroup M] [Module ℂ M]
  {T : (H → ℂ) → Module.End ℂ M} {J : Type}

private theorem polyFn_single (ψ : J → H → ℂ) (w : List J) (c : ℂ) (f : H → ℂ) :
    polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f :=
  Finsupp.sum_single_index (zero_smul _ _)

private theorem polyFn_zero (ψ : J → H → ℂ) (f : H → ℂ) : polyFn K ψ 0 f = 0 :=
  Finsupp.sum_zero_index

private theorem polyFn_add (ψ : J → H → ℂ) (s t : List J →₀ ℂ) (f : H → ℂ) :
    polyFn K ψ (s + t) f = polyFn K ψ s f + polyFn K ψ t f :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

private theorem word_mem (ψ : J → H → ℂ) (f : H → ℂ) (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K) (w : List J) :
    wordFn K ψ w f ∈ Hecke ℂ K := by
  have h := hmem (Finsupp.single w 1)
  rwa [polyFn_single, one_smul] at h

private theorem T_word (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hmem : ∀ w, wordFn K ψ w f ∈ Hecke ℂ K) (w : List J) :
    T (wordFn K ψ w f) = (w.map fun j => T (ψ j)).prod * T f := by
  induction w with
  | nil => simp [wordFn]
  | cons j w ih =>
    have h : wordFn K ψ (j :: w) f = Formalism.UG.conv K (ψ j) (wordFn K ψ w f) := rfl
    rw [h, hmul _ (hψ j) _ (hmem w), ih, List.map_cons, List.prod_cons, mul_assoc]

private theorem T_poly (hT0 : T 0 = 0) (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (hlin : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, ∀ c : ℂ, T (c • f + f') = c • T f + T f')
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K)
    (s : List J →₀ ℂ) : T (polyFn K ψ s f) = wop (fun j => T (ψ j)) s * T f := by
  induction s using Finsupp.induction_linear with
  | zero => rw [polyFn_zero, hT0, UpperTheory.Gal.CertificateRingHomMap.wop_zero, zero_mul]
  | add s t hs ht =>
    have h : polyFn K ψ (s + t) f = (1 : ℂ) • polyFn K ψ s f + polyFn K ψ t f := by
      rw [one_smul, polyFn_add]
    rw [h, hlin _ (hmem s) _ (hmem t), one_smul, hs, ht, UpperTheory.Gal.CertificateRingHomMap.wop_add, add_mul]
  | single w c =>
    have h : polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f + 0 := by
      rw [polyFn_single, add_zero]
    rw [h, hlin _ (word_mem ψ f hmem w) _ (Submodule.zero_mem _), hT0, add_zero,
      T_word hmul ψ hψ f (word_mem ψ f hmem) w, UpperTheory.Gal.CertificateRingHomMap.wop_single, smul_mul_assoc]

private theorem T_pow (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (u e : H → ℂ) (hu : u ∈ Hecke ℂ K) (hmem : ∀ n, powFn K u e n ∈ Hecke ℂ K) (n : ℕ) :
    T (powFn K u e n) = T u ^ n * T e := by
  induction n with
  | zero => simp [powFn]
  | succ n ih =>
    have h : powFn K u e (n + 1) = Formalism.UG.conv K u (powFn K u e n) := Function.iterate_succ_apply' _ _ _
    rw [h, hmul _ hu _ (hmem n), ih, pow_succ', mul_assoc]

private theorem C_pow {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f))
    (u e : H → ℂ) (hu : u ∈ Hecke ℂ K) (he : C e) (hmem : ∀ n, powFn K u e n ∈ Hecke ℂ K) (n : ℕ) :
    C (powFn K u e n) := by
  induction n with
  | zero => exact he
  | succ n ih =>
    have h : powFn K u e (n + 1) = Formalism.UG.conv K u (powFn K u e n) := Function.iterate_succ_apply' _ _ _
    rw [h]
    exact hid _ hu _ (hmem n) ih

private theorem C_word {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f))
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hf : C f)
    (hmem : ∀ w, wordFn K ψ w f ∈ Hecke ℂ K) (w : List J) : C (wordFn K ψ w f) := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact hid _ (hψ j) _ (hmem w) ih

private theorem C_poly {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f)) (h0 : C 0)
    (hlin : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, ∀ c : ℂ, C f → C f' → C (c • f + f'))
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hf : C f)
    (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K) (s : List J →₀ ℂ) : C (polyFn K ψ s f) := by
  induction s using Finsupp.induction_linear with
  | zero => rw [polyFn_zero]; exact h0
  | add s t hs ht =>
    have h : polyFn K ψ (s + t) f = (1 : ℂ) • polyFn K ψ s f + polyFn K ψ t f := by
      rw [one_smul, polyFn_add]
    rw [h]
    exact hlin _ (hmem s) _ (hmem t) _ hs ht
  | single w c =>
    have h : polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f + 0 := by
      rw [polyFn_single, add_zero]
    rw [h]
    exact hlin _ (word_mem ψ f hmem w) _ (Submodule.zero_mem _) _
      (C_word hid ψ hψ f hf (word_mem ψ f hmem) w) h0

private theorem hecke_relation_image (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (ψ : J → H → ℂ) (e u u' : H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K) (hu : u ∈ Hecke ℂ K)
    (hu' : u' ∈ Hecke ℂ K) (hrel : Rel (Formalism.UG.conv K) ψ e u u') (hB : Formalism.UG.conv K u e ∈ Hecke ℂ K)
    (hA : ∀ j, Formalism.UG.conv K (ψ j) e ∈ Hecke ℂ K) :
    Rel (· * ·) (fun j => T (ψ j)) (T e) (T u) (T u') := by
  refine ⟨?_, fun j => ?_, ?_, fun j j' => ?_, fun j => ?_, ?_⟩
  · have h := congrArg T hrel.idem
    rwa [hmul _ he _ he] at h
  · have h := congrArg T (hrel.eT j)
    rwa [hmul _ he _ (hA j), hmul _ (hψ j) _ he] at h
  · have h := congrArg T hrel.eu
    rwa [hmul _ he _ hB, hmul _ hu _ he] at h
  · have h := congrArg T (hrel.TT j j')
    rwa [hmul _ (hψ j) _ (hA j'), hmul _ (hψ j') _ he, hmul _ (hψ j') _ (hA j), hmul _ (hψ j) _ he] at h
  · have h := congrArg T (hrel.uT j)
    rwa [hmul _ hu _ (hA j), hmul _ (hψ j) _ he, hmul _ (hψ j) _ hB, hmul _ hu _ he] at h
  · have h := congrArg T hrel.inv
    rwa [hmul _ hu' _ hB, hmul _ hu _ he] at h

end Abstract

private theorem forms_fin {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V)
    (hf : Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H))) :
    FiniteDimensional ℂ (HeckeTraceForms.forms ι K ξ) := by
  haveI := hf
  obtain ⟨r, hr⟩ : ∃ r : DoubleCoset.Quotient (ι.range : Set H) (K : Set H) → H, ∀ g : H,
      ∃ γ : Γ, ∃ k ∈ K, g = ι γ * r (DoubleCoset.mk ι.range K g) * k := by
    refine ⟨fun q => Quotient.out q, fun g => ?_⟩
    obtain ⟨h, ⟨γ, rfl⟩, k, hk, e⟩ := (@DoubleCoset.eq _ _ ι.range K _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk ι.range K g))
    exact ⟨γ, k, hk, e⟩
  let L : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] (DoubleCoset.Quotient (ι.range : Set H) (K : Set H) → V) :=
    { toFun := fun φ q => (φ : H → V) (r q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective L ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  apply Subtype.ext
  funext g
  have h0 : (φ : H → V) (r (DoubleCoset.mk ι.range K g)) = 0 :=
    congrFun hφ (DoubleCoset.mk ι.range K g)
  obtain ⟨γ, k, hk, e⟩ := hr g
  have h1 : (φ : H → V) g = ξ γ ((φ : H → V) (r (DoubleCoset.mk ι.range K g))) := by
    conv_lhs => rw [e]
    rw [φ.2.2 k hk, φ.2.1]
  rw [h1, h0, map_zero]
  rfl

def SpecOfF : Prop := ForPlaces fun p _ G Lv C R => Finite (DFCls G) →
  ∀ (D : Datum p) (L : GlobalTheory.LKGeo.Link D G) (lam : (D.F →+* ℂ) → Fin G.n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V), IsWt L lam ξ →
    ∀ (J : Type) (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (e u u' : G.GAf → ℂ),
    (∀ j, ψ j ∈ Hecke ℂ Lv.K.toSubgroup) → e ∈ Hecke ℂ Lv.K.toSubgroup → u ∈ Hecke ℂ Lv.K.toSubgroup →
    u' ∈ Hecke ℂ Lv.K.toSubgroup → Rel (Formalism.UG.conv Lv.K.toSubgroup) ψ e u u' → C e →
    (∀ n : ℕ, 1 ≤ n → ∃ A : Set G.GAf, (∀ g ∈ A, R g ∧ RegAf G g) ∧ (∀ j a, ψ j a ≠ 0 → ∀ g ∈ A, a * g ∈ A) ∧
      ∀ g, powFn Lv.K.toSubgroup u e n g ≠ 0 → g ∈ A) →
    HasEig G ξ Lv.K.toSubgroup ψ θ e → ∃ n : ℕ, 1 ≤ n ∧ Spec L lam Lv.K.toSubgroup ψ θ (powFn Lv.K.toSubgroup u e n)

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.specOfF :
    UpperTheory.Gal.Spc.SpecOfF := by
  intro p _ G hGa Lv k _ _ _ _ _ _ _ P H _ _ _ _ S k₁ _ _ P₁ hfin D L lam V _ _ _ ξ hwt J ψ θ e u u' hψ he hu hu' hrel hCe hA hEig
  have hW := words p G Lv J ψ e u u' hψ he hu hrel
  have hp : ∀ n, powFn Lv.K.toSubgroup u e n ∈ Hecke ℂ Lv.K.toSubgroup := fun n => (hW n).1
  have hpoly : ∀ n s, polyFn Lv.K.toSubgroup ψ s (powFn Lv.K.toSubgroup u e n) ∈ Hecke ℂ Lv.K.toSubgroup :=
    fun n => (hW n).2.1
  obtain ⟨hCi, hC0, hCl⟩ := cuspIdeal p G hGa Lv k P H S k₁ P₁
  obtain ⟨q₀, Φ₀, hΦ₀, hne, hΦe, hΦψ⟩ := clsMove p G V ξ Lv.K.toSubgroup J ψ θ e hEig
  letI : Fintype (DFCls G) := Fintype.ofFinite _
  have hop := fun q : DFCls G => opAlg p G Lv V ξ (Quot.out q)
  choose T hT0 hT using hop
  haveI hfd' : ∀ q : DFCls G, FiniteDimensional ℂ (HeckeTraceForms.forms (Quot.out q).emb (Lv.K.toSubgroup.prod (Kp G))
      (ξ.comp (grp G (Quot.out q).β).subtype)) := fun q =>
    forms_fin (Quot.out q).emb _ _ (GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level p G hGa Lv (Kp G) (Subgroup.Commensurable.refl _) (Quot.out q))
  have hmul : ∀ q, ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup,
      T q (Formalism.UG.conv Lv.K.toSubgroup f f') = T q f * T q f' := fun q f hf f' hf' => ((hT q f hf).2.2 f' hf').1
  have hlin : ∀ q, ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup, ∀ c : ℂ,
      T q (c • f + f') = c • T q f + T q f' := fun q f hf f' hf' => ((hT q f hf).2.2 f' hf').2
  have hB : Formalism.UG.conv Lv.K.toSubgroup u e ∈ Hecke ℂ Lv.K.toSubgroup := hp 1
  have hAj : ∀ j, Formalism.UG.conv Lv.K.toSubgroup (ψ j) e ∈ Hecke ℂ Lv.K.toSubgroup := fun j =>
    word_mem ψ _ (hpoly 0) [j]
  have key := specAlg (DFCls G) J
    (fun q => HeckeTraceForms.forms (Quot.out q).emb (Lv.K.toSubgroup.prod (Kp G)) (ξ.comp (grp G (Quot.out q).β).subtype))
    (fun q j => T q (ψ j)) (fun q => T q e) (fun q => T q u) (fun q => T q u') θ
    (fun q => hecke_relation_image (hmul q) ψ e u u' hψ he hu hu' hrel hB hAj)
    ⟨q₀, ⟨Φ₀, hΦ₀⟩, fun h => hne (congrArg Subtype.val h),
      Subtype.ext (((hT q₀ e he).1 ⟨Φ₀, hΦ₀⟩).trans hΦe),
      fun j => Subtype.ext (((hT q₀ (ψ j) (hψ j)).1 ⟨Φ₀, hΦ₀⟩).trans (hΦψ j))⟩
  obtain ⟨n, hn, a, ha⟩ := key
  refine ⟨n, hn, (hW n).2.2.1, V, inferInstance, inferInstance, inferInstance, ξ, hwt, fun s hs => ⟨a, ?_, ?_⟩⟩
  · obtain ⟨A, hAR, hAψ, hAp⟩ := hA n hn
    have hsup := (hW n).2.2.2 A hAψ hAp
    have hCF : S.Cusp (polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n)) :=
      C_poly hCi hC0 hCl ψ hψ _ (C_pow hCi u e hu hCe hp n) (hpoly n) _
    have hR : ∀ g, polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n) g ≠ 0 →
        (P₁.at g).charpoly.Separable := fun g hg => (hAR g (hsup _ g hg)).1
    exact ⟨fun g hg => (hAR g (hsup _ g hg)).2,
      vanPairs p G hGa Lv k P H S k₁ P₁ _ (hpoly n _) hCF hR,
      vanForms p G hGa Lv k P H S k₁ P₁ _ (hpoly n _) hCF hR⟩
  · have hq : ∀ q : DFCls G, (Quot.out q).trace ξ Lv.K.toSubgroup
        (polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n)) (Kp G) (oneP G) =
        LinearMap.trace ℂ _ (wop (fun j => T q (ψ j)) (wmul a s) * (T q u ^ n * T q e)) := fun q => by
      rw [(hT q _ (hpoly n _)).2.1, T_poly (hT0 q) (hmul q) (hlin q) ψ hψ _ (hpoly n),
        T_pow (hmul q) u e hu hp n]
    unfold dTrace
    rw [finsum_eq_sum_of_fintype]
    simp only [hq]
    exact ha s hs
end
end

