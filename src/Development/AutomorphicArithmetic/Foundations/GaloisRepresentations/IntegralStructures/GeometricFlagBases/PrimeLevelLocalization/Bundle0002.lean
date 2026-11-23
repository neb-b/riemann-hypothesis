module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p} (F : Frame S)

theorem inId_span {ι : Type} [Fintype ι] (w : Plc E) (b : ι → 𝓞 E) (y : w.adicCompletion E) (hy : InId w (Ideal.span (Set.range b)) y) :
    ∃ z : ι → w.adicCompletionIntegers E, y = ∑ j, algebraMap (𝓞 E) (w.adicCompletion E) (b j) * (z j : w.adicCompletion E) := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [Ideal.map_span, ← Set.range_comp, Ideal.mem_span_range_iff_exists_fun] at hz
  obtain ⟨c, rfl⟩ := hz
  refine ⟨c, ?_⟩
  rw [AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem InId.add {w : Plc E} {𝔟 : Ideal (𝓞 E)} {y y' : w.adicCompletion E} (h : InId w 𝔟 y) (h' : InId w 𝔟 y') : InId w 𝔟 (y + y') := by
  obtain ⟨z, hz, rfl⟩ := h
  obtain ⟨z', hz', rfl⟩ := h'
  exact ⟨z + z', add_mem hz hz', rfl⟩

theorem InId.zero (w : Plc E) (𝔟 : Ideal (𝓞 E)) : InId w 𝔟 0 := ⟨0, zero_mem _, rfl⟩

theorem InId.mul {w : Plc E} {𝔟 : Ideal (𝓞 E)} {y y' : w.adicCompletion E} (h : InId w 𝔟 y) (h' : y' ∈ w.adicCompletionIntegers E) :
    InId w 𝔟 (y * y') := by
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨z * ⟨y', h'⟩, Ideal.mul_mem_right _ _ hz, rfl⟩

theorem InId.sum {ι : Type} {w : Plc E} {𝔟 : Ideal (𝓞 E)} (s : Finset ι) {y : ι → w.adicCompletion E} (h : ∀ i, InId w 𝔟 (y i)) :
    InId w 𝔟 (∑ i ∈ s, y i) :=
  Finset.sum_induction y (InId w 𝔟) (fun _ _ => InId.add) (InId.zero w 𝔟) fun i _ => h i

theorem InId.of_mem (w : Plc E) {𝔟 : Ideal (𝓞 E)} {x : 𝓞 E} (hx : x ∈ 𝔟) : InId w 𝔟 (algebraMap (𝓞 E) (w.adicCompletion E) x) :=
  ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩

theorem mem_idHat_iff (𝔟 : Ideal (𝓞 E)) (v) :
    v ∈ idHat S.D 𝔟 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i, InId w 𝔟 (F.vec w v i) := by
  constructor
  · intro hv w hw i
    induction hv using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨x, hx, u, hu, rfl⟩ := hz
      rw [F.vec_mul w hw x u]
      exact (InId.of_mem w hx).mul ((F.vec_hat u).1 hu w hw i)
    | zero => rw [map_zero]; exact InId.zero w 𝔟
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact ha.add hb
    | neg a _ ha =>
      rw [map_neg]
      simpa using ha.mul (neg_mem (one_mem _))
  · intro h
    obtain ⟨r, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian 𝔟)
    have hb' : Ideal.span (Set.range b) = 𝔟 := hb
    have key : ∀ (w : Plc E) (i : Fin n), ∃ z : Fin r → w.adicCompletionIntegers E, (p : 𝓞 E) ∉ w.asIdeal →
        F.vec w v i = ∑ j, algebraMap (𝓞 E) (w.adicCompletion E) (b j) * (z j : w.adicCompletion E) := fun w i => by
      by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
      · exact ⟨0, fun h' => absurd hw h'⟩
      · obtain ⟨z, hz⟩ := inId_span w b _ (hb' ▸ h w hw i)
        exact ⟨z, fun _ => hz⟩
    choose z hz using key
    choose u hu using fun j : Fin r => F.vec_surj (fun w i => (z w i j : w.adicCompletion E)) fun w i => (z w i j).2
    have e : v = ∑ j, mulF S.D (b j) (u j) := by
      refine sub_eq_zero.1 (F.vec_inj _ fun w hw => ?_)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_eq_zero]
      funext i
      rw [hz w i hw, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [F.vec_mul w hw (b j) (u j), hu j w hw]; rfl
    rw [e]
    refine sum_mem fun j _ => AddSubgroup.subset_closure ⟨b j, hb' ▸ Ideal.subset_span ⟨j, rfl⟩, u j, (F.vec_hat _).2 fun w hw i => ?_, rfl⟩
    rw [hu j w hw]
    exact (z w i j).2

theorem basis_vec (k : Fin n) : ∃ v ∈ LaHat S.D, ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → F.vec w v = Pi.single k 1 := by
  have hi : ∀ (w : Plc E) i, (Pi.single k 1 : Fin n → w.adicCompletion E) i ∈ w.adicCompletionIntegers E := fun w i => by
    rw [Pi.single_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  obtain ⟨v, hv⟩ := F.vec_surj (fun w => Pi.single k 1) hi
  exact ⟨v, (F.vec_hat v).2 fun w hw i => by rw [hv w hw]; exact hi w i, hv⟩

theorem nsmul_integ_iff (g : GUf E n) (c : ℕ) : (∀ v ∈ LaHat S.D, c • S.L.actG (F.j g) v ∈ LaHat S.D) ↔
    ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k, (c : w.adicCompletion E) * F.cmp w g i k ∈ w.adicCompletionIntegers E := by
  constructor
  · intro h w hw i k
    obtain ⟨v, hv, e⟩ := basis_vec F k
    have := (F.vec_hat _).1 (h v hv) w hw i
    rw [map_nsmul, F.vec_act w hw, e w hw] at this
    simpa [Frame.cmp] using this
  · intro h v hv
    refine (F.vec_hat _).2 fun w hw i => ?_
    rw [map_nsmul, F.vec_act w hw]
    show c • ∑ k, F.cmp w g i k * F.vec w v k ∈ _
    rw [nsmul_eq_mul, Finset.mul_sum]
    exact sum_mem fun k _ => by rw [← mul_assoc]; exact mul_mem (h w hw i k) ((F.vec_hat v).1 hv w hw k)

theorem integ_iff (g : GUf E n) :
    Integ S.L (F.j g) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k, F.cmp w g i k ∈ w.adicCompletionIntegers E := by
  simpa only [Integ, one_smul, Nat.cast_one, one_mul] using nsmul_integ_iff F g 1

theorem cmp_inv (w : Plc E) (g : GUf E n) : F.cmp w g⁻¹ = ((F.a w * comp w g * (F.a w)⁻¹)⁻¹).val := by
  unfold Frame.cmp
  rw [map_inv]
  congr 1
  group

end

theorem dict_holds : Dict := by
  intro E _ _ _ A n p _ S F g
  have hmul : ∀ (g h : S.G.GAf) v, S.L.actG (g * h) v = S.L.actG g (S.L.actG h v) := fun g h v => by
    rw [map_mul, Module.End.mul_apply]
  refine ⟨integ_iff F g, ?_, fun 𝔟 _ => ?_, fun c => ?_⟩
  · have h1 : F.j g ∈ S.L.KN 1 ↔ Integ S.L (F.j g) ∧ Integ S.L (F.j g⁻¹) := by
      rw [map_inv]
      refine ⟨fun h => ⟨integ_of_mem h, integ_of_mem (inv_mem h)⟩, fun h => ?_⟩
      have key : ∀ g, Integ S.L g → S.L.CongOne 1 g := fun g hg v hv => ⟨S.L.actG g v - v, sub_mem (hg v hv) hv, by simp⟩
      exact ⟨key _ h.1, key _ h.2⟩
    rw [h1, integ_iff, integ_iff]
    constructor
    · intro h w hw
      exact (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w _).2 ⟨h.1 w hw, cmp_inv F w g ▸ h.2 w hw⟩
    · intro h
      refine ⟨fun w hw => ((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w _).1 (h w hw)).1, fun w hw => ?_⟩
      rw [cmp_inv]
      exact ((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w _).1 (h w hw)).2
  · have hv : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ v, F.vec w (S.L.actG (F.j g) v - v) = (F.cmp w g - 1) *ᵥ F.vec w v := fun w hw v => by
      rw [map_sub, F.vec_act w hw, Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
    constructor
    · intro h w hw i k
      obtain ⟨v, hv', e⟩ := basis_vec F k
      have := (mem_idHat_iff F 𝔟 _).1 (h v hv') w hw i
      rw [hv w hw, e w hw] at this
      simpa using this
    · intro h v hv'
      refine (mem_idHat_iff F 𝔟 _).2 fun w hw i => ?_
      rw [hv w hw]
      exact InId.sum Finset.univ fun k => (h w hw i k).mul ((F.vec_hat v).1 hv' w hw k)
  · rw [← nsmul_integ_iff]
    refine forall₂_congr fun v _ => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
    · rintro ⟨v', hv', e⟩
      rwa [← map_nsmul, ← e, ← hmul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]
    · rw [map_nsmul, ← hmul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]

end UpperTheory.Gal.Int.Geo.Pl
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PCongOf
section
open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

theorem UpperTheory.Gal.Int.Geo.Pl.congOf_of :
    LevBasic → TjOK → TjIdx → CongOf := by
  intro hL hT hI E _ _ _ A n p _ S F x hx N w σ J L _ g θ ϑ hD hm
  obtain ⟨-, h2, h3, -⟩ := hL p S.D S.G S.L
  obtain ⟨l1, l2, l3, l4, l5⟩ := σ.lv
  refine ⟨σ.q, σ.r, Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, σ.K₀, σ.atp,
    ⟨ordCompl[σ.q] N.1, σ.𝔞, l1, l2, l3, l4, l5, rfl⟩, σ.isLev,
    h2 _ _ _ _ (h3 N.1) σ.isLev ((Ideal.span_singleton_le_iff_mem _).2 σ.mem), σ.mem, hD, ?_⟩
  intro i hi
  obtain ⟨j, ⟨hin, hK, hH, hM⟩, hθ⟩ := hm i hi
  refine ⟨j, hK, (hT E A n p S F x hx N w σ i hin _ hH).2, ?_, ?_, ?_⟩
  · rw [hM]; exact Dvd.intro_left _ rfl
  · intro _
    exact hI E A n p S F x hx N w σ i hin _ hH
  · rw [hθ, idx, hK]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PGoodOf
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

namespace UpperTheory.Gal.Int.Geo.Pl.GoodPlacesAlt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {N : Lv p}

private def Row (q : ℕ) (r : ℤ) (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)) (K₀ : Subgroup G.GAf) (𝔴 : Ideal (𝓞 D.F)) (g : Mem L N) : Prop :=
  ∃ (c : ℕ) (𝔞' : Ideal (𝓞 D.F)) (K₁ : Subgroup G.GAf) (h₁ h₂ : G.GAf) (N₁ : Lv p), LevAt D q r 𝔴 (N₀ * c) 𝔞' ∧
      IsLev L (Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞') K₁ ∧ 𝔞' ≤ 𝔞 ∧ L.KN g.M.1 ≤ K₁ ∧
      ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞' ∧
      (∀ u ∈ K₀, ∃ x ∈ g.K, x ∈ K₀ ∧ x⁻¹ * u ∈ K₁) ∧ g.h = h₁ * h₂ ∧ Integ L h₁ ∧ Integ L h₂ ∧
      (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = c • v) ∧ ((N₁.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞' ∧
      (∀ k ∈ g.K, ∀ u ∈ L.KN g.M.1, h₂ * k * u * (h₂ * k)⁻¹ ∈ L.KN N₁.1) ∧
      (∀ u ∈ L.KN N₁.1, h₁ * u * h₁⁻¹ ∈ L.KN N.1) ∧
      (h₁ = 1 ∨ ∃ (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal ∧ uId D q r ≤ 𝔴' ∧ 𝔞' ≤ 𝔞 * 𝔴' ∧ i ≤ D.n ∧
        Ideal.absNorm 𝔴' ^ i ∣ N₁.1 ∧ IsTjElt L q r 𝔴' i h₁)

private theorem kn_le
    (hle : ∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K')
    (hKN : ∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N))
    {𝔟 : Ideal (𝓞 D.F)} {K : Subgroup G.GAf} {M : ℕ} (hK : IsLev L 𝔟 K) (hM : (M : 𝓞 D.F) ∈ 𝔟) : L.KN M ≤ K :=
  hle _ _ _ _ (hKN M) hK ((Ideal.span_singleton_le_iff_mem _).2 hM)

private theorem row_trans
    (hle : ∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K')
    (hKN : ∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N))
    {q : ℕ} {r : ℤ} {N₀ : ℕ} {𝔞 𝔴 : Ideal (𝓞 D.F)} {K₀ K₁ : Subgroup G.GAf} {c : ℕ}
    (hlv : LevAt D q r 𝔴 N₀ 𝔞) (hN : ((N.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞)
    (hc : 0 < c) (hcq : c.Coprime q) (hcp : c.Coprime p)
    (hK₁ : IsLev L (Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞) K₁)
    (g : Mem L N) (hM : g.M.1 = N.1 * c)
    (hback : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG g.h v' = c • v)
    (hx : ∀ u ∈ K₀, ∃ x ∈ g.K, x ∈ K₀ ∧ x⁻¹ * u ∈ K₁) : Row q r N₀ 𝔞 K₀ 𝔴 g := by
  obtain ⟨h3, hq, hp, hv, e, he⟩ := hlv
  have hmem : ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞 := by
    obtain ⟨a, ha, ea⟩ := Ideal.mem_span_singleton_mul.1 hN
    refine Ideal.mem_span_singleton_mul.2 ⟨a, ha, ?_⟩
    rw [hM]; push_cast; rw [← ea]; ring
  refine ⟨c, 𝔞, K₁, 1, g.h, N, ⟨le_trans h3 (Nat.le_mul_of_pos_right _ hc), Nat.coprime_mul_iff_left.2 ⟨hq, hcq⟩,
    Nat.coprime_mul_iff_left.2 ⟨hp, hcp⟩, hv, e, he⟩, hK₁, le_rfl, kn_le hle hKN hK₁ hmem, hmem, hx,
    (one_mul _).symm, integ_of_mem (one_mem _), g.int, hback, hN, fun k hk u hu => g.adm k hk u hu, ?_, Or.inl rfl⟩
  intro u hu
  simpa using hu

private theorem row_near
    (hex : ∀ 𝔟, ∃ K, IsLev L 𝔟 K)
    (hle : ∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K')
    (hKN : ∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N))
    (hnorm : ∀ 𝔟 K, IsLev L 𝔟 K → ∀ k ∈ L.KN 1, ∀ u ∈ K, k * u * k⁻¹ ∈ K)
    {q : ℕ} {r : ℤ} {N₀ : ℕ} {𝔞 𝔴 𝔴' : Ideal (𝓞 D.F)} {K₀ : Subgroup G.GAf} {i : ℕ}
    (hlv : LevAt D q r 𝔴 N₀ 𝔞) (hN : ((N.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞)
    (hmax : 𝔴.IsMaximal) (hmax' : 𝔴'.IsMaximal) (hne : 𝔴' ≠ 𝔴) (hu : uId D q r ≤ 𝔴')
    (hi : 0 < i) (hin : i ≤ D.n) (g : Mem L N) (hK : g.K = K₀) (hM : g.M.1 = N.1 * Ideal.absNorm 𝔴' ^ i)
    (hT : IsTjElt L q r 𝔴' i g.h) : Row q r N₀ 𝔞 K₀ 𝔴 g := by
  obtain ⟨h3, hq, hp, hv, e, he⟩ := hlv
  obtain ⟨K₁, hK₁⟩ := hex (Ideal.span {((N₀ * 1 : ℕ) : 𝓞 D.F)} * (𝔞 * 𝔴'))
  have hmem : ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * (𝔞 * 𝔴') := by
    rw [← mul_assoc, hM]
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hn : ((Ideal.absNorm 𝔴' : ℕ) : 𝓞 D.F) ∈ 𝔴' := Ideal.absNorm_mem 𝔴'
    have : ((N.1 * Ideal.absNorm 𝔴' ^ (i + 1) : ℕ) : 𝓞 D.F)
        = (((N.1 : ℕ) : 𝓞 D.F) * ((Ideal.absNorm 𝔴' : ℕ) : 𝓞 D.F) ^ i) * ((Ideal.absNorm 𝔴' : ℕ) : 𝓞 D.F) := by
      push_cast; ring
    rw [this]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hN) hn
  have hmem1 : ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * 1 : ℕ) : 𝓞 D.F)} * (𝔞 * 𝔴') := by
    simpa using hmem
  refine ⟨1, 𝔞 * 𝔴', K₁, g.h, 1, g.M, ⟨by simpa using h3, by simpa using hq, by simpa using hp, ?_, e + 1, ?_⟩, hK₁,
    Ideal.mul_le_left, kn_le hle hKN hK₁ hmem1, hmem1, ?_, (mul_one _).symm, g.int, integ_of_mem (one_mem _), ?_,
    hmem, ?_, ?_, Or.inr ⟨𝔴', i, hmax', hu, le_rfl, hin, by rw [hM]; exact Dvd.intro_left _ rfl, hT⟩⟩
  · exact Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.2 hv)
      (Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne hmax' hmax hne)))
  · rw [pow_succ]; exact Ideal.mul_mono he hu
  · intro u hu'
    exact ⟨u, hK ▸ hu', hu', by simpa using one_mem K₁⟩
  · intro v hv'
    exact ⟨v, hv', by simp⟩
  · intro k hk u hu'
    have := hnorm _ _ (hKN g.M.1) k (g.le_one hk) u hu'
    simpa using this
  · intro u hu'
    have := g.adm 1 (one_mem _) u hu'
    simpa using this

private theorem absNorm_nat {E : Type} [Field E] [NumberField E] (q : ℕ) :
    Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 E)}) = q ^ Module.finrank ℤ (𝓞 E) := by
  rw [Ideal.absNorm_span_singleton, show ((q : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (q : ℤ) by simp,
    Algebra.norm_algebraMap]
  simp [Int.natAbs_pow]

end UpperTheory.Gal.Int.Geo.Pl.GoodPlacesAlt

open UpperTheory.Gal.Int.Geo.Pl.GoodPlacesAlt in
theorem UpperTheory.Gal.Int.Geo.Pl.goodOf_of :
    LevBasic → TjOK → ProjLev → GoodOf := by
  intro hL hT hP E _ _ _ A n p _ S F x hx N v σ J L' _ g θ hD hj
  obtain ⟨hex, hle, hKN, -, hnorm, -⟩ := hL p S.D S.G S.L
  refine ⟨σ.q, σ.r, ordCompl[σ.q] N.1, σ.𝔞, σ.K₀, σ.atp, σ.lv, σ.isLev, kn_le hle hKN σ.isLev σ.mem, σ.mem, hD,
    fun j => ?_⟩
  have hK₀ : IsLev S.L (Ideal.span {((ordCompl[σ.q] N.1 * 1 : ℕ) : 𝓞 E)} * σ.𝔞) σ.K₀ := by
    simpa using σ.isLev
  change Row σ.q σ.r (ordCompl[σ.q] N.1) σ.𝔞 σ.K₀ v.asIdeal (g j)
  rcases hj j with ⟨hK, hM, hh⟩ | ⟨w, σ', i, hne, hc, hi, hK, hH, hM⟩
  · refine row_trans hle hKN σ.lv σ.mem one_pos (Nat.coprime_one_left _) (Nat.coprime_one_left _) hK₀ (g j) (by simp [hM]) ?_ ?_
    · intro v' hv'
      refine ⟨S.L.actG (g j).h⁻¹ v', integ_of_mem (inv_mem hh) v' hv', ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      simp
    · intro u hu
      exact ⟨1, one_mem _, one_mem _, by simpa using hu⟩
  · obtain ⟨hI, hTj⟩ := hT E A n p S F x hx N w σ' i hi _ hH
    by_cases hq : σ.q = σ'.q
    · obtain ⟨hr, ha⟩ := hc hq
      have hKe : σ'.K₀ = σ.K₀ := by
        have h' := σ'.isLev
        rw [← hq, ← ha] at h'
        exact Subgroup.ext fun y => (h' y).trans (σ.isLev y).symm
      rw [hKe] at hK
      have hat := σ'.atp
      rw [← hq, ← hr] at hTj hat
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · refine row_trans hle hKN σ.lv σ.mem one_pos (Nat.coprime_one_left _) (Nat.coprime_one_left _) hK₀ (g j) (by simpa using hM) ?_ ?_
        · intro v' hv'
          obtain ⟨y, hy, e⟩ := hTj.back v' hv'
          exact ⟨y, hy, by simpa using e⟩
        · intro u hu
          exact ⟨1, one_mem _, one_mem _, by simpa using hu⟩
      · exact row_near hex hle hKN hnorm σ.lv σ.mem σ.atp.max hat.max
          (fun e => hne (HeightOneSpectrum.ext e)) hat.le hpos hi (g j) hK hM hTj
    · have hat := σ'.atp
      have hqw : ((σ'.q : ℕ) : 𝓞 E) ∈ w.asIdeal := hat.le (Ideal.subset_span (Set.mem_insert _ _))
      have hdvd : Ideal.absNorm w.asIdeal ∣ σ'.q ^ Module.finrank ℤ (𝓞 E) := by
        have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hqw)
        rwa [absNorm_nat] at this
      obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hat.prime).1 hdvd
      have hcpow : Ideal.absNorm w.asIdeal ^ i = σ'.q ^ (f * i) := by rw [hf, pow_mul]
      obtain ⟨K₁, hK₁⟩ := hex (Ideal.span {((ordCompl[σ.q] N.1 * σ'.q ^ (f * i) : ℕ) : 𝓞 E)} * σ.𝔞)
      have hcq : (σ'.q ^ (f * i)).Coprime σ.q :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hat.prime σ.atp.prime).2 (Ne.symm hq))
      have hcp : (σ'.q ^ (f * i)).Coprime p :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hat.prime (Fact.out)).2 hat.ne)
      refine row_trans hle hKN σ.lv σ.mem (pow_pos hat.prime.pos _) hcq hcp hK₁ (g j) (by rw [hM, hcpow]) ?_ ?_
      · rw [← hcpow]; exact hTj.back
      · intro u hu
        obtain ⟨y, hy, e⟩ := hP E A n p S F N v σ σ'.q (f * i) hat.prime (Ne.symm hq) K₁ hK₁ u hu
        exact ⟨y, hK ▸ kn_le hle hKN σ'.isLev σ'.mem hy, kn_le hle hKN σ.isLev σ.mem hy, e⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PInIdBasic
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

section

variable {E : Type} [Field E] [NumberField E] (w : Plc E)

private theorem valued_algebraMap_adicCompletionIntegers_eq_intValuation (r : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) r : w.adicCompletionIntegers E) :
      w.adicCompletion E) = w.intValuation r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E) w r]
  exact HeightOneSpectrum.adicCompletion.valued_coe _ _ _

theorem inId_iff_le (𝔟 : Ideal (𝓞 E)) (y : w.adicCompletion E) : InId w 𝔟 y ↔ ∃ x ∈ 𝔟, Valued.v y ≤ w.intValuation x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ Submodule.span _ _ at hz
    induction hz using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨x, hx, rfl⟩ := ha
      exact ⟨x, hx, (valued_algebraMap_adicCompletionIntegers_eq_intValuation w x).le⟩
    | zero => exact ⟨0, 𝔟.zero_mem, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨x1, h1, e1⟩ := ha
      obtain ⟨x2, h2, e2⟩ := hb
      have hab : Valued.v (((a + b : w.adicCompletionIntegers E)) : w.adicCompletion E) ≤
          max (Valued.v (a : w.adicCompletion E)) (Valued.v (b : w.adicCompletion E)) :=
        Valuation.map_add Valued.v (a : w.adicCompletion E) (b : w.adicCompletion E)
      rcases le_total (w.intValuation x1) (w.intValuation x2) with h | h
      · exact ⟨x2, h2, hab.trans (max_le (e1.trans h) e2)⟩
      · exact ⟨x1, h1, hab.trans (max_le e1 (e2.trans h))⟩
    | smul c a _ ha =>
      obtain ⟨x, hx, e⟩ := ha
      refine ⟨x, hx, ?_⟩
      have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
      have hm : Valued.v (((c • a : w.adicCompletionIntegers E)) : w.adicCompletion E) =
          Valued.v (c : w.adicCompletion E) * Valued.v (a : w.adicCompletion E) :=
        Valuation.map_mul Valued.v (c : w.adicCompletion E) (a : w.adicCompletion E)
      rw [hm]
      exact (mul_le_of_le_one_left' hc).trans e
  · rintro ⟨x, hx, hle⟩
    have hy : y ∈ w.adicCompletionIntegers E :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hle.trans (w.intValuation_le_one x))
    by_cases h0 : w.intValuation x = 0
    · rw [h0, le_zero_iff, Valuation.zero_iff] at hle
      exact ⟨0, Ideal.zero_mem _, by simp [hle]⟩
    · set a : w.adicCompletionIntegers E := algebraMap (𝓞 E) (w.adicCompletionIntegers E) x with ha_def
      have ha : Valued.v (a : w.adicCompletion E) = w.intValuation x := valued_algebraMap_adicCompletionIntegers_eq_intValuation w x
      have ha0 : (a : w.adicCompletion E) ≠ 0 := by
        intro h
        apply h0
        rw [← ha, h, map_zero]
      have hq : y / (a : w.adicCompletion E) ∈ w.adicCompletionIntegers E := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, ha]
        exact div_le_one_of_le₀ hle zero_le'
      refine ⟨⟨_, hq⟩ * a, Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hx), ?_⟩
      simp only [MulMemClass.coe_mul]
      exact div_mul_cancel₀ y ha0

end

end UpperTheory.Gal.Int.Geo.Pl
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PInIdUnit
section
noncomputable section

open NumberField IsDedekindDomain
open UpperTheory.Gal.CertificateRingHomMap (Plc)

namespace UpperTheory.Gal.Int.Geo.Pl

private theorem isUnit_algebraMap_adicCompletionIntegers_of_not_mem (E : Type) [Field E] [NumberField E] (w : Plc E) (s : 𝓞 E)
    (hs : s ∉ w.asIdeal) :
    IsUnit (algebraMap (𝓞 E) (HeightOneSpectrum.adicCompletionIntegers E w) s) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change Valued.v ((algebraMap (𝓞 E) E s : E) : HeightOneSpectrum.adicCompletion E w) = 1
  rw [HeightOneSpectrum.adicCompletion.valued_coe, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  exact hs

theorem inIdUnit_holds : InIdUnit := by
  intro E _ _ w b c hc y
  obtain ⟨s, hsc, hsw⟩ := hc
  have htop : Ideal.map (algebraMap (𝓞 E) (HeightOneSpectrum.adicCompletionIntegers E w)) c = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsc) (isUnit_algebraMap_adicCompletionIntegers_of_not_mem E w s hsw)
  unfold InId
  rw [Ideal.map_mul, htop, Ideal.mul_top]

end UpperTheory.Gal.Int.Geo.Pl

end
end

