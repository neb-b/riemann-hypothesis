module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasepointFreeSectionTupleAmpleArith
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.NoethGens

theorem exists_cover (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hP : IsAmpleLB P.L.B) (d : ℕ) :
    ∀ Z : Set X, IsClosed Z → (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) < d) →
      ∃ (e : ℕ) (x : Fin d → X.functionField), 0 < e ∧ (∀ l, x l ∈ P.H e 0) ∧ ∀ z ∈ Z, ∃ l, z ∈ NV P e 0 (x l) := by
  induction d with
  | zero =>
    intro Z _ h
    refine ⟨1, Fin.elim0, one_pos, fun l => l.elim0, fun z hz => ?_⟩
    exfalso
    have h₁ := h (ringChar (X.residueField z))
    have hne : Nonempty ↥(Z ∩ fib X (ringChar (X.residueField z))) := ⟨⟨z, hz, rfl⟩⟩
    obtain ⟨w⟩ := hne
    have hne' : Nonempty (IrreducibleCloseds ↥(Z ∩ fib X (ringChar (X.residueField z)))) :=
      ⟨⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₂ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Z ∩ fib X (ringChar (X.residueField z))) :=
      Order.krullDim_nonneg
    exact absurd h₁ (not_lt.2 (by simpa using h₂))
  | succ d ih =>
    intro Z hZ h
    obtain ⟨e, he, f, hf, hlt⟩ := _root_.GlobalTheory.HSAmp.exists_sec_fibre_dim_lt k X p D hX P hP d Z hZ fun ℓ =>
      ENat.WithBot.lt_add_one_iff.1 (by simpa using h ℓ)
    have hnf := _root_.GlobalTheory.HSAmp.nv_rules k X p P e 0 f hf
    obtain ⟨e', x, he', hx, hc⟩ := ih (Z \ NV P e 0 f) (hZ.sdiff hnf.1) hlt
    have c₁ : ((e' * e : ℕ) : ℤ) = (e' : ℤ) * (e : ℤ) := Nat.cast_mul _ _
    have c₂ : ((e' * e : ℕ) : ℤ) = (e : ℤ) * (e' : ℤ) := by rw [c₁, mul_comm]
    refine ⟨e' * e, Fin.cons (f ^ e') fun l => x l ^ e, Nat.mul_pos he' he, fun l => ?_, fun z hz => ?_⟩
    · refine Fin.cases ?_ (fun l => ?_) l
      · have := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 f hf e').1
        rw [mul_zero, ← c₁] at this
        simpa only [Fin.cons_zero] using this
      · have := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e' 0 (x l) (hx l) e).1
        rw [mul_zero, ← c₂] at this
        simpa only [Fin.cons_succ] using this
    · by_cases hzf : z ∈ NV P e 0 f
      · refine ⟨0, ?_⟩
        have := hnf.2.2.1 e' he'
        rw [mul_zero, ← c₁] at this
        rw [Fin.cons_zero, this]
        exact hzf
      · obtain ⟨l, hl⟩ := hc z ⟨hz, hzf⟩
        refine ⟨l.succ, ?_⟩
        have := (_root_.GlobalTheory.HSAmp.nv_rules k X p P e' 0 (x l) (hx l)).2.2.1 e he
        rw [mul_zero, ← c₂] at this
        rw [Fin.cons_succ, this]
        exact hl

theorem exists_gens (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hP : IsAmpleLB P.L.B) :
    ∃ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x := by
  obtain ⟨e, x, he, hx, hc⟩ := exists_cover k X p D hX P hP (D + 1) Set.univ isClosed_univ fun ℓ => by
    rw [Set.univ_inter, Nat.cast_add_one]
    exact ENat.WithBot.lt_add_one_iff.2 ((_root_.GlobalTheory.IntFib.fib_structure k X p D hX).2.2.2.1 ℓ)
  exact ⟨e, x, he, hx, fun z => hc z trivial⟩

end GlobalTheory.HSAmp.NoethGens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonScaleThetaConstantsAtTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.TraitScale

theorem isUnit_natCast {o V : Type} [CommRing o] [CommRing V] [IsDomain V] (f : o →+* FractionRing V)
    (hf : ∀ a, f a ∈ Set.range (algebraMap V (FractionRing V))) {m : ℕ} (hm : IsUnit (m : o)) : IsUnit (m : V) := by
  obtain ⟨u, hu⟩ := hm.exists_right_inv
  obtain ⟨v, hv⟩ := hf u
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)
  rw [map_mul, map_natCast, hv, map_one, ← map_natCast f, ← map_mul, hu, map_one]

theorem thList_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m N : ℕ} {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂) {T : Over S} (h₁ : Over.mk x₁ ⟶ T)
    (h₂ : Over.mk x₂ ⟶ T) (he : h₁.left = h₂.left) (θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T))
    {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x₁ (VVRank.pullS G _ h₁ θ) pt c) :
    ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ (VVRank.pullS G _ h₂ θ) pt' c := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext he
  exact ⟨pt, H⟩

theorem level_odd {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    Odd (S.r * S.N) ∧ 3 ≤ S.r * S.N := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  have ho : Odd (S.r * S.N) := by
    rw [hj, ρ.N_eq]
    exact (ρ.n_odd.pow).mul (ρ.n_odd.pow.pow)
  refine ⟨ho, ?_⟩
  have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
  obtain ⟨t, ht⟩ := ho
  omega

theorem exists_scale : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (m N : ℕ) (e : Fin N → Ω), Odd m → 3 ≤ m → IsUnit (m : o) → N = m ^ (4 * S.g) → SymE ρ m e → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (emb : Ω →+* FractionRing V), (∀ a : o, emb (algebraMap o Ω a) ∈ Set.range (algebraMap V (FractionRing V))) → ∃ (K : Type) (_ : Field K) (io : FractionRing V →+* K) (N' : ℕ) (c : Fin N → K) (c' : Fin N' → K) (a : K), a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) ∧ (∀ j, io (emb (e j)) = symTup c j) ∧ (∀ x, ∃ b, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ m N e hm hm3 hmu hN hE V _ _ _ hV emb hemb
  letI := ρ.P.isAb.comm
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let i : S.R →+* K := (io.comp emb).comp S.R.val.toRingHom
  let y : Sp (FractionRing V) ⟶ Sp S.R := spMap (emb.comp S.R.val.toRingHom)
  have hmV : IsUnit (m : V) := isUnit_natCast (emb.comp (algebraMap o Ω)) hemb hmu
  have hkV : IsUnit ((S.r * S.N : ℕ) : V) := isUnit_natCast (emb.comp (algebraMap o Ω)) hemb S.unit
  have ne : ∀ {k : ℕ}, IsUnit (k : V) → (k : K) ≠ 0 := fun h => by
    have := h.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨hko, hk3⟩ := level_odd ρ
  have hfib : PolFib ρ.P.A ρ.P.L S.g (spMap i ≫ 𝟙 (Sp S.R)) :=
    ρ.g_eq ▸ GlobalTheory.UMin.FibExist.polFib_of_point _ ρ.P K _
  obtain ⟨pt, c, H⟩ := _root_.GlobalTheory.UMin.exists_thList _ ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen S.g m N K _
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) hm (ne hmV) hN hfib
  obtain ⟨pt', c', H'⟩ := _root_.GlobalTheory.UMin.exists_thList _ ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen S.g (S.r * S.N) _ K _
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) hko (ne hkV) rfl hfib
  have hx : spMap i ≫ 𝟙 (Sp S.R) = spMap io ≫ y := by
    rw [Category.comp_id, ← spMap_comp]
  have H2 : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap io ≫ y) c c' :=
    hx ▸ (⟨_, pt, pt', GlobalTheory.UMin.isGenSec_real_pull o Ω S ρ K i, H, H'⟩ :
      HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) c c')
  obtain ⟨P, α, -, hα, hiso⟩ := GlobalTheory.UMin.FibExist.polFib_of_point _ ρ.P (FractionRing V) y
  have hS : (letI := P.isAb.comm; HypS P.A P.L) := by
    letI := P.isAb.comm
    exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ ρ.P.A P.A y α ρ.P.L P.L ρ.P.isLB P.isLB hα hiso ρ.hypS
  obtain ⟨a, ha, h₁, h₂⟩ := GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait _ ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen V hV y P α hα hiso hS K io m (S.r * S.N)
    _ _ c c' hm hm3 hmV hko hk3 hkV H2
  obtain ⟨r₁, r₂⟩ := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o Ω S ρ K i _ pt' c' H'
  refine ⟨K, inferInstance, io, _, c, c', a, ha, h₁, h₂, ?_, r₁, r₂⟩
  have hz : spMap i ≫ 𝟙 (Sp S.R) = spMap (io.comp emb) ≫ spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R) := by
    rw [← Category.assoc, ← spMap_comp]
  obtain ⟨q, Hq⟩ := thList_transport hz _
    ((Over.homMk (spMap (io.comp emb)) rfl : Over.mk (spMap (io.comp emb) ≫ spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R)) ⟶
      Over.mk (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R))) ≫
      (Over.homMk (spMap S.R.val.toRingHom) rfl :
        Over.mk (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R)) ⟶ Over.mk (𝟙 (Sp S.R))))
    (spMap_comp _ _) _ H
  rw [← ThetaRuleCompare.pullS_comp] at Hq
  exact hE.2.2 K (io.comp emb) q c Hq

end GlobalTheory.SiegTh.TraitScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveWeightSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.GenKer

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R' : Type} [CommRing R'] [Algebra ℚ R'] {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (u : Sp B ⟶ Sp A) : ∃ β : A →+* B, u = spMap β :=
  ⟨(Spec.preimage u).hom, by simp [spMap]⟩

theorem charZero_of_hom {k : Type} [Field k] (β : R' →+* k) : CharZero k :=
  charZero_of_injective_ringHom (β.comp (algebraMap ℚ R')).injective

theorem pow_eq_one_geom {gb : GBase D.toG R'} {N : ℕ} {t : S ⟶ Sp R'} (o : GObj gb N t) (e : ℕ)
    (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S)
    (g : Over.mk x₀ ⟶ o.A) (M : ℕ) (hM : 0 < M) (hn : g ^ M = 1)
    (hg : ∃ u : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, u.IsGen) :
    g ^ e = 1 := by
  obtain ⟨β, hβ⟩ := exists_spMap (x₀ ≫ t)
  haveI := charZero_of_hom β
  obtain ⟨I, -⟩ := o.geom k x₀ β hβ
  obtain ⟨y, hy⟩ : ∃ y : D.La, I.ev M y = g := (I.onto M hM g).1 hn
  have key : ∀ z : D.La, (M : ℤ) ∣ D.EF y z := by
    intro z
    have hm : 0 < M * 2 := by omega
    have ha : I.ev (M * 2) y ^ 2 = g := by rw [I.tower M 2 hM two_pos y, hy]
    have hc := GlobalTheory.WeilSqKer.weilIs_eq_one S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ (M * 2)
      (Nat.cast_ne_zero.2 hm.ne') _ _ ((I.onto _ hm _).2 ⟨y, rfl⟩) ((I.onto _ hm _).2 ⟨z, rfl⟩) (ha ▸ hg) _
      (I.isom _ hm y z)
    have h1 : I.ζ (M * 2) ^ (2 * D.EF y z) = 1 :=
      GlobalTheory.Ex.Specialise.unitOn_bijective.1 (hc.trans (map_one _).symm)
    have h3 := ((I.ζ_prim (M * 2) hm).zpow_eq_one_iff_dvd _).1 h1
    have h4 : (M : ℤ) * 2 ∣ D.EF y z * 2 := by
      rw [mul_comm (D.EF y z)]; exact_mod_cast h3
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / M
      map_add' := fun u v => by
        rw [map_add (f := _), Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (M : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = M • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev M y ^ e := by rw [hy]
    _ = I.ev M (e • y) := (KerBy.ev_nsmul (La := D.La) _ (I.add M) e y).symm
    _ = 1 := (I.ker M hM _).2 ⟨w, hyw⟩

theorem exists_coprime_pow_eq_one (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R']
    (gb : GBase D.toG R') (N : ℕ) (_hN : 3 ≤ N) (S : Scheme.{0}) (t : S ⟶ Sp R') (o : GObj gb N t) :
    ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ u : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, u.IsGen) → x ^ e = 1 := by
  obtain ⟨e, he, hEF⟩ := D.perfP
  refine ⟨e, he, fun T x hx => ?_⟩
  apply Over.OverMorphism.ext
  refine T.left.affineCover.hom_ext _ _ fun i => ?_
  obtain ⟨B, ⟨u⟩⟩ : ∃ B : CommRingCat.{0}, Nonempty (T.left.affineCover.X i ≅ Spec B) :=
    ⟨_, ⟨(T.left.affineCover.X i).isoSpec⟩⟩
  rw [← cancel_epi u.inv]
  let a : Sp B ⟶ T.left := u.inv ≫ T.left.affineCover.f i
  let a' : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  have hx' := KerBy.gen_comp S o.A o.P T _ a' x hx
  obtain ⟨M, hM, hxM⟩ := GlobalTheory.T.isTorsion_of_birigidified_bundle_trivial_on_slice S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ o.symm o.ample B (a ≫ T.hom) _ hx'
  have hu : IsUnit ((M : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((M : ℕ) : R') := by
      simpa using (IsUnit.mk0 (M : ℚ) (Nat.cast_ne_zero.2 hM.ne')).map (algebraMap ℚ R')
    simpa using (h0.map (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom).map t.appTop.hom
  have h := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points S o.A o.ab M hu _ _ hxM e fun k _ _ ξ =>
    pow_eq_one_geom o e hEF k _ _ M hM (by rw [← MonObj.comp_pow, hxM, MonObj.comp_one])
      (KerBy.gen_comp S o.A o.P _ _ _ _ hx')
  have h' : a' ≫ x ^ e = a' ≫ 1 := by rw [MonObj.comp_pow, h, MonObj.comp_one]
  have h'' : a ≫ (x ^ e).left = a ≫ (1 : T ⟶ o.A).left := congrArg (fun z => z.left) h'
  exact (Category.assoc _ _ _).symm.trans (h''.trans (Category.assoc _ _ _))

end GlobalTheory.UPel.HT.GenKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionGaloisEquivariantLabelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_galois_equivariant_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → OneTrait D₁.toPre A lab → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))) (lab₂ : Labels D₂.toPre A₂), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ OneTrait D₂.toPre A₂ lab₂ ∧ GalEqN n lab₂ := by
  first | exact @GlobalTheory.Mum.exists_finExt_galEqN | exact GlobalTheory.Mum.exists_finExt_galEqN | (intros; apply GlobalTheory.Mum.exists_finExt_galEqN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionTraitUniformisingMumfordBun
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_finExt_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂), FinExt ρ ∧ ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  obtain ⟨W, _, _, _, φ, GW, _, _, βW, βW₂, DW, AW, UW, hW, hφi, hφl, hpbW, hsqW, hlamW⟩ :=
    _root_.GlobalTheory.Mum.TraitUnif.exists_trait_unif_lam R hR G hG A gen hgen PP hPP
  obtain ⟨ga, α, α₂, hga, hpbα, hsqα, hlamα, hcompα⟩ :=
    _root_.GlobalTheory.Mum.genLam_pull_of_unif R hR G hG A gen hgen PP hPP W φ GW βW βW₂ DW AW UW hW hφi hφl hpbW hsqW hlamW

  have : CharZero R := hR.2
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨K', _, io, Ω', _, j, l, A₁, α₁, α₁₂, p, hio, hlio, hpb₁, hsq₁, hlam₁, hp₁, hp₂, hpL⟩ :=
    _root_.GlobalTheory.SymFinExt.exists_finite_ext (FractionRing R) (FractionRing W) ga A AW α α₂ hpbα hsqα hlamα
  have hcomp : ∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r)) := by
    intro r
    have h := DFunLike.congr_fun hlio (algebraMap R (FractionRing R) r)
    simp only [RingHom.comp_apply] at h
    rw [h, hga]
  obtain ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hρ, hW₂, hσ, hσl, hφ₂i, hφ₂l, hsq, hi, hj₂, hl₂⟩ :=
    _root_.GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait R W hR hW φ hφi hφl K' Ω' io j l hio hcomp
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ, hρ, ?_⟩
  intro G₂ _ _ β β₂ hpb₂ hsq₂
  obtain ⟨A₂, gen₂, q, hgen₂, hext₂, hpbq, hlamq, hcompq⟩ :=
    _root_.GlobalTheory.Mum.transport_extLam R G A gen hgen PP hPP K' io A₁ α₁ α₁₂ hpb₁ hsq₁ hlam₁ R₂ ρ i hρ.2.1 hi G₂ β β₂ hpb₂ hsq₂
  obtain ⟨GW', _, _, βW', τ, DW', AW', UW', κ, hpbW', hpbτ, hβτ, hκ, hLτ⟩ :=
    _root_.GlobalTheory.Mum.unif_trait_baseChange R R₂ W W₂ ρ φ σ φ₂ hR hW hW₂ hσ hσl hsq hφ₂i G hG G₂ β hpb₂ GW βW hpbW DW AW UW
  refine ⟨A₂, gen₂, W₂, inferInstance, inferInstance, inferInstance, φ₂, GW', inferInstance, inferInstance,
    βW', DW', AW', UW', κ, hgen₂, hext₂, hW₂, hφ₂i, hφ₂l, hpbW', hκ, ?_⟩
  exact _root_.GlobalTheory.unif_bundle_generic_descent R W R₂ W₂ K' Ω' φ ρ σ φ₂ io j l i j₂ hφi hρ.2.1 hσ.2.1 hφ₂i hsq hcomp hi hj₂ hl₂
    G A gen GW βW DW AW UW α hpbW hcompα A₁ α₁ p hpb₁ hp₁ hp₂ hpL G₂ β A₂ gen₂ q hpb₂ hpbq hlamq hcompq
    GW' βW' τ DW' AW' UW' κ hpbW' hpbτ hβτ hκ hLτ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifference
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem nu_conjPt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    {f : X.functionField} (hf : f ∈ P.H a b) {σ σ' : k →+* ℂ} {y : CxPts p σ} {y' : CxPts p σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) : P.nu a b σ' y' f = P.nu a b σ y f := by
  have hi := mem_pick (P.L.φ σ).isLB y
  have hj := mem_pick (P.A.φ σ).isLB y
  have hi' := CxPts.mem_ptsIn_conj h hi
  have hj' := CxPts.mem_ptsIn_conj h hj
  have hreg := hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
  rw [GlobalTheory.VolBr.nu_eq k X p P a b f hf σ' y' _ _ hi' hj', GlobalTheory.VolBr.nu_eq k X p P a b f hf σ y _ _ hi hj,
    ratVal_conj h hreg, Complex.norm_conj, P.L.conj σ σ' _ y y' h hi, P.A.conj σ σ' _ y y' h hj]

theorem exists_isCan_bdd : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∃ u : SmFn p, IsCan P e n x u ∧ ∀ σ y, |u.u σ y| ≤ B := by
  intro k _ X _ p D hX P e x hx
  obtain ⟨B, hB, hb⟩ := _root_.GlobalTheory.HSAmp.can_bound k X p D hX P e x hx
  refine ⟨B, hB, fun n hn => ⟨⟨fun σ y => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)),
    fun σ y => _root_.GlobalTheory.HSAmp.cInfAt_canWeight k X p P D e x hx n hn σ y, fun σ σ' i y y' h _ => ?_⟩, fun σ y => rfl, fun σ y => hb n hn σ y⟩⟩
  change ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ' y' (x l) ^ (2 * n)) =
    ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))
  simp only [nu_conjPt P _ _ (hx.mem _) h]

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorAlgebraisationReductions
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem res_compat_of_gm {Z B : Scheme.{0}} {N : LB B} (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ)
    (h : ∀ z i i', b z ∈ N.U i → b z ∈ N.U i' → gm (𝟙 _) z _ (s i) = gm b z _ (N.g i i') * gm (𝟙 _) z _ (s i'))
    (i i' : N.ι) :
    res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) =
      pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i') := by
  apply unit_ext
  intro z hz
  have hz' : b z ∈ N.U i ⊓ N.U i' := hz
  rw [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_pull (𝟙 _) b z _ hz', Category.id_comp]
  exact h z i i' hz'.1 hz'.2

theorem appLE_eq_of_gm {Y Y' B : Scheme.{0}} {N : LB B} (β : Y ⟶ Y') (b : Y ⟶ B) (b' : Y' ⟶ B) (hβ : β ≫ b' = b)
    (i : N.ι) (s : Γ(Y, b ⁻¹ᵁ N.U i)ˣ) (s' : Γ(Y', b' ⁻¹ᵁ N.U i)ˣ)
    (h : ∀ z, b z ∈ N.U i → gm β z _ s' = gm (𝟙 _) z _ s) :
    (β.appLE (b' ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hβ]; exact le_rfl)).hom s'.val = s.val := by
  apply TopCat.Presheaf.section_ext Y.sheaf
  intro z hz
  have := congrArg Units.val (h z hz)
  have hz2 : β z ∈ b' ⁻¹ᵁ N.U i := by rw [← hβ] at hz; exact hz
  rw [gm_val β z _ hz2, gm_val (𝟙 Y) z _ hz] at this
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  exact this

theorem exists_isGen_of_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : LB X.left), N.IsLB → ∀ s : ∀ e (i : N.ι), Γ((Y e).left, b e ⁻¹ᵁ N.U i)ˣ, (∀ e z i i', b e z ∈ N.U i → b e z ∈ N.U i' → gm (𝟙 _) z _ (s e i) = gm (b e) z _ (N.g i i') * gm (𝟙 _) z _ (s e i')) → (∀ e z i, b e z ∈ N.U i → gm (β e) z _ (s (e + 1) i) = gm (𝟙 _) z _ (s e i)) → ∃ t : LB.Gen N, t.IsGen := by
  intro R _ _ I hI X hX Y β b hb hβ N hN s hs hsβ
  obtain ⟨G, q, u, hqa, hql, hu, hU⟩ := _root_.GlobalTheory.generatorScheme_affine_finiteType X.left N hN
  have hex := fun e => hU (Y e).left (b e) (s e) (res_compat_of_gm (b e) (s e) (fun z i i' => hs e z i i'))
  choose f hfq hfu using fun e => (hex e).exists
  have hfβ : ∀ e, β e ≫ f (e + 1) = f e := fun e =>
    (hex e).unique ⟨by rw [Category.assoc, hfq, hβ], fun i => by
        rw [← Scheme.Hom.appLE_comp_appLE (β e) (f (e + 1)) (q ⁻¹ᵁ N.U i) (b (e + 1) ⁻¹ᵁ N.U i) (b e ⁻¹ᵁ N.U i)
          (by rw [← hfq (e + 1)]; exact le_rfl) (by rw [← hβ e]; exact le_rfl),
          CommRingCat.comp_apply, hfu (e + 1) i]
        exact appLE_eq_of_gm (β e) (b e) (b (e + 1)) (hβ e) i (s e i) (s (e + 1) i) (hsβ e · i)⟩
      ⟨hfq e, hfu e⟩
  let Z : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ X.hom)
  have H := _root_.GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms
  obtain ⟨g, hg, -⟩ := H R I hI X Z hX (inferInstanceAs (IsSeparated (q ≫ X.hom)))
    (inferInstanceAs (LocallyOfFiniteType (q ≫ X.hom))) (inferInstanceAs (QuasiCompact (q ≫ X.hom)))
    Y β b hb hβ f (fun e => by
      show f e ≫ q ≫ X.hom = _
      rw [← Category.assoc, hfq, (hb e).w]) hfβ
  have hgq : g.left ≫ q = 𝟙 X.left := by
    have hH := H R I hI X X hX inferInstance inferInstance inferInstance Y β b hb hβ b (fun e => (hb e).w) hβ
    have h1 := hH.unique (y₁ := Over.homMk (g.left ≫ q) (by rw [Category.assoc]; exact Over.w g))
      (y₂ := 𝟙 X) (fun e => by
        show b e ≫ (g.left ≫ q) = b e
        rw [← Category.assoc, hg e, hfq e])
      (fun e => by rw [Over.id_left, Category.comp_id])
    exact congrArg CommaMorphism.left h1
  have hpt : ∀ x, q (g.left x) = x := fun x => by rw [← Scheme.Hom.comp_apply, hgq]; rfl
  have hle : ∀ i, N.U i ≤ g.left ⁻¹ᵁ (q ⁻¹ᵁ N.U i) := fun i x hx => by
    show q (g.left x) ∈ N.U i
    rw [hpt]; exact hx
  refine ⟨⟨fun i => res (hle i) (pullU g.left _ (u i))⟩, fun i j => ?_⟩
  apply unit_ext
  intro x hx
  have hx' : q (g.left x) ∈ N.U i ⊓ N.U j := by rw [hpt]; exact hx
  have key := congrArg (gm g.left x (q ⁻¹ᵁ (N.U i ⊓ N.U j))) (hu i j)
  rw [map_mul, gm_res _ x _ hx', gm_res _ x _ hx', gm_pull g.left q x _ hx', hgq] at key
  show gm (𝟙 _) x _ (res _ (res (hle i) (pullU g.left _ (u i)))) =
    gm (𝟙 _) x _ (N.g i j * res _ (res (hle j) (pullU g.left _ (u j))))
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx.1, gm_res _ x _ hx, gm_res _ x _ hx.2,
    gm_pull (𝟙 _) g.left x _ (hle i hx.1), gm_pull (𝟙 _) g.left x _ (hle j hx.2),
    Category.id_comp]
  exact key

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] (S : ThetaSys o Ω) (S' : ThetaSys o' Ω') (ρ : S.Real) (ρ' : S'.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (y₁ : S'.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a → IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' → LBIso P₀.L (u.A.L.pull a) → LBIso P₀.L (u'.A.L.pull a') → ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ r, u.PsiNorm χ r ↔ u'.PsiNorm (e χ) r) ∧ ∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left → w ≫ a' = x'.left → CongMod m pk'.y (e pk.y) := by
  first | exact @GlobalTheory.UnifTorsK.main | exact GlobalTheory.UnifTorsK.main | (intros; apply GlobalTheory.UnifTorsK.main <;> assumption)
end

