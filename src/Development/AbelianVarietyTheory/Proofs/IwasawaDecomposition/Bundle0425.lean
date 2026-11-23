module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointChartMulTwist
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

theorem carries_mul_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {g h : GL (Fin N) (TensorProduct F E (Formalism.L2.Herm.Af F))} {L : Submodule (𝓞 E) (Fin N → E)}
    (hg : Formalism.L2.Herm.Carries g L L) (hh : Formalism.L2.Herm.Carries h L L) : Formalism.L2.Herm.Carries (g * h) L L := by
  intro x
  rw [hg x, hh, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]


set_option maxHeartbeats 1000000 in
theorem admissibleBasePoint_chart_mul_twist : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∀ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) → (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) → (a = I.mu0 → ∀ β, t β = 1) → GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun β => k0 (g β) * t β) := by
  intro B X I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR g t hstd hoff h0
  refine ⟨fun β => ?_, fun β v hT hQ hd => ?_, fun β P r j hr => ?_⟩
  · obtain ⟨p, hp, hN⟩ := hR.k_std (g β)
    obtain ⟨q, hq, hN'⟩ := hstd β
    have h1 := hp.lat
    have h2 := hq.lat
    rw [hN] at h1
    rw [hN'] at h2
    refine ⟨p, ⟨mul_mem hp.uni hq.uni, ?_, fun P => ?_, fun w => ?_, fun P => ?_⟩, hN⟩
    · rw [hN]
      exact carries_mul_self h1 h2
    · exact absurd P.2 (Finset.notMem_empty _)
    · exact absurd w.2 (Finset.notMem_empty _)
    · exact absurd P.2 (Finset.notMem_empty _)
  · have hq0 : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty _
    have hk : bc (prV (E := B.host.E) v) (k0 (g β)) = 1 :=
      hR.k_off (g β) v hT (by rintro ⟨P, hP, -⟩; rw [hq0] at hP; simp at hP) (Or.inl rfl)
    have ht : bc (prV (E := B.host.E) v) (t β) = 1 := by
      rcases hd with rfl | hd
      · rw [h0 rfl β, map_one]
      · exact hoff β v (Or.inr hd)
    have hm := map_mul (bc (prV (E := B.host.E) v)) (k0 (g β)) (t β)
    rw [hk, ht, one_mul] at hm
    exact hm
  · have hv : (B.T u : 𝓞 B.host.F) ∈ (P.1.under (𝓞 B.host.F)).asIdeal := by
      have := T_mem_vT (GlobalTheory.BasePrimes.primes_ok B X).1 u P
      rw [HeightOneSpectrum.under, Ideal.mem_comap, map_natCast]
      exact this
    have ht := hoff β _ (Or.inl hv)
    have ht' := (map_inv (bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F)))) (t β)).trans (by rw [ht, inv_one])
    have hent : ∀ r l, adAt B.host.F P.1 (((t β)⁻¹ : GA B (B.R.N i)).1 r l) = if r = l then 1 else 0 := by
      intro r l
      have e := congrArg (fun g => g.1 r l) ht'
      simp only [bc, Units.coe_map, Units.val_one, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e
      split_ifs with h
      · subst h
        exact FullDt.adAt_eq_one_of_prV P.1 (by simpa using e)
      · exact TilX.adAt_eq_zero_of_prV P.1 _ (by simpa [Matrix.one_apply_ne h] using e)
    have key : adAt B.host.F P.1 (((k0 (g β) * t β)⁻¹ : GA B (B.R.N i)).1 r j) =
        adAt B.host.F P.1 (((k0 (g β))⁻¹ : GA B (B.R.N i)).1 r j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply, map_sum]
      simp only [map_mul, hent, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key]
    exact hR.k_T (g β) P r j hr

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelTwistTrivialLocalMove
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChTwRead

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def noFr (p : DecoF E n ST SG Q) : DecoF E n ST SG ∅ :=
  ⟨(p.deco, fun P => absurd P.2 (Finset.notMem_empty _)), fun P => absurd P.2 (Finset.notMem_empty _)⟩

theorem isPtOf_iff (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) :
    IsPtOf hc g p ↔ (g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) ∧
      ∀ (P : Q) (i j : Fin n), adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E _ (p.fr P (Pi.single j 1) i) := by
  have key := PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g (noFr p) rfl
  constructor
  · intro h
    exact ⟨key.1 ⟨h.uni, h.lat, h.f, h.be, fun P => absurd P.2 (Finset.notMem_empty _)⟩, h.fr⟩
  · rintro ⟨h, h'⟩
    have h2 := key.2 h
    exact ⟨h2.uni, h2.lat, h2.f, h2.be, h'⟩

theorem adAt_congr_prV (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : prV (E := E) (P.under (𝓞 F)) z = prV (E := E) (P.under (𝓞 F)) z') : adAt F P z = adAt F P z' := by
  have h0 := TilX.adAt_eq_zero_of_prV P (z - z') (by rw [map_sub, h, sub_self])
  rwa [map_sub, sub_eq_zero] at h0

theorem exists_pt_of_agree {g₁ g' : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h₁ : IsPtOf hc g₁ p)
    (hg' : g' ∈ UAd hc n)
    (hv : ∀ P ∈ Q, bc (prV (E := E) (P.under (𝓞 F))) g' = bc (prV (E := E) (P.under (𝓞 F))) g₁) :
    ∃ q : DecoF E n ST SG Q, IsPtOf hc g' q := by
  obtain ⟨⟨-, hd1⟩, -⟩ := (isPtOf_iff hc g₁ p).1 h₁
  have hloc : ∀ P ∈ Q, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.deco.1.N := by
    intro P hP
    rw [hd1]
    exact updn_mem_loc (v := P.under (𝓞 F)) (P := P) rfl (hv P hP)
  refine ⟨⟨(⟨decoRaw ST SG g', decorated_lattice_exists hc n ST SG g' hg'⟩, p.fr), fun P x => ?_⟩, ?_⟩
  · show p.fr P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) ↔ _
    rw [hloc P.1 P.2]
    exact p.2 P x
  · refine (isPtOf_iff hc g' _).2 ⟨⟨hg', rfl⟩, fun P i j => ?_⟩
    show _ = algebraMap E _ (p.fr P (Pi.single j 1) i)
    rw [← h₁.fr P i j]
    apply adAt_congr_prV
    exact congrArg (fun g => g.1 i j) (hv P.1 P.2)

theorem isPtOf_mul {g g₁ s : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q} (h : GLG (E := E) (n := n) (SG := SG))
    (hq : q.deco.1 = p.deco.1.act 1 h) (hg : IsPtOf hc g p) (hg₁ : IsPtOf hc g₁ p) (hs : IsPtOf hc (g₁ * s) q) :
    IsPtOf hc (g * s) q := by
  obtain ⟨⟨hgu, hdg⟩, hfg⟩ := (isPtOf_iff hc g p).1 hg
  obtain ⟨⟨hu1, hd1⟩, hf1⟩ := (isPtOf_iff hc g₁ p).1 hg₁
  obtain ⟨⟨hsu, hds⟩, hfs⟩ := (isPtOf_iff hc (g₁ * s) q).1 hs
  have hsU : s ∈ UAd hc n := by
    have e : s = g₁⁻¹ * (g₁ * s) := by group
    rw [e]
    exact mul_mem (inv_mem hu1) hsu
  obtain ⟨hJ, -⟩ := mem_congruence_of_action hc ST SG hsu hu1 h (by rw [← hds, hq, hd1])
  have hK := mem_principal_of_same_decoration hc n ST SG hu1 hgu (hd1.symm.trans hdg)
  have hc' := K1_conj hc n ST SG ⟨_, hJ⟩ (a := ⟨g₁⁻¹ * g, principal_le_adelic_unitary hc n ST SG hK⟩)
    (Subgroup.mem_subgroupOf.2 hK)
  rw [Subgroup.mem_subgroupOf] at hc'
  have e : g * s = (g₁ * s) * ((((g₁ * s)⁻¹ * g₁) * (g₁⁻¹ * g)) * ((g₁ * s)⁻¹ * g₁)⁻¹) := by group
  have hdr : decoRaw ST SG (g * s) = decoRaw ST SG (g₁ * s) := by
    rw [e]
    exact decorated_lattice_mul_principal hc n ST SG _ hc'
  refine (isPtOf_iff hc (g * s) q).2 ⟨⟨mul_mem hgu hsU, hds.trans hdr.symm⟩, fun P i j => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hfs P i j, Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_mul, hfg P i l, hf1 P i l]

end GlobalTheory.Mem.Col2.ChTwRead

namespace GlobalTheory.Mem.Col2.TC.ChTw

theorem locMv_of_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : Ch → GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)), x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) → (∀ v, I.UnderQ a v → bc (prV (E := B.host.E) v) x = 1) → x ∈ U (chOf c) → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ := by
  intro B X I hI _ u a i _ Ch chOf Lb U chi y st k hR c x hx hx1 hxU
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := hpk.uni
  have hg' : y c * x * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) := by group
    rw [e]
    exact mul_mem hp.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
  have hv : ∀ P ∈ I.Q a, bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * x * k (chOf c)) =
      bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * k (chOf c)) := by
    intro P hP
    have h1 := hx1 (P.under (𝓞 B.host.F)) ⟨P, hP, rfl⟩
    simp only [map_mul, h1, mul_one]
  obtain ⟨q, hq⟩ := ChTwRead.exists_pt_of_agree B.sp.cm hp hg' hv
  obtain ⟨κ, hκ1, hκq, hκc⟩ := (hR.lev c x q hq).1 hxU
  refine ⟨κ, hκ1, hκc, fun g hg => ?_⟩
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hγ : κ.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hκ1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  · refine ChTwRead.isPtOf_mul B.sp.cm κ.2.1.1 ?_ hg hp (by rw [e, hκq]; exact hq)
    show ((κ.1, (κ.2.1 : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs))) • ((I.stp u a i).rep c).1.1.deco).1 = _
    rw [hγ]
    rfl
end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffFieldRootsOfUnityTypePrimesHermitianStages
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Cls

theorem coeffField_rootsOfUnity_typePrimes_hermitianStages : ∀ X : Stages, GlobalTheory.Core.Cls.RootsG X.toD7 := by
  intro X i
  have hp : Nat.Prime (X.B.host.g i) := X.B.host.g_prime i
  obtain ⟨z, -, hz⟩ := X.B.roots_Ks (X.B.host.g i * (X.B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : X.B.host.g i * (X.B.host.g i - 1) ≠ 0 :=
    mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (X.B.host.g i * (X.B.host.g i - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := X.B.embLL) ?_ X.B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have hpos : 0 < X.B.host.g i * (X.B.host.g i - 1) := Nat.pos_of_ne_zero hne
  exact ⟨⟨z ^ (X.B.host.g i - 1), hprim.pow hpos (mul_comm _ _)⟩, ⟨z ^ X.B.host.g i, hprim.pow hpos rfl⟩⟩

end GlobalTheory.Core.Cls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjHeckeFamIApply
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.RowAd.Inert

theorem conj_heckeFamI_apply {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (C : Formalism.L2.Col.CoefPk X n (Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : Formalism.L2.Col.LevFam X.E X.K n SG)
    (hS : (Formalism.L2.Col.formGSD C Λ).Ok) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Formalism.L2.Col.LevOffI ST SG S0 × List ℕ)
    (f : ((Formalism.L2.Col.formGSD C Λ).toCSD hS).Forms) (d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    ((((Formalism.L2.Col.formGSD C Λ).res hS).symm ((((Formalism.L2.Col.formGSD C Λ).res hS).conj
      (Formalism.L2.Col.heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y)) f) : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) d =
      ∑ e ∈ d.inertNb y.1.1.asIdeal y.2, ((((Formalism.L2.Col.formGSD C Λ).res hS).symm f : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) e := by
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [Formalism.L2.Col.heckeFamI_formPts_apply]
  rfl

theorem colIn3_heckeRI_apply {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R)
    (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
    (τ : TupF TU) (q : ↑((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).okI τ) × List ℕ)
    (f : ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.MtildeCSD τ).Forms) (d : (Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).D) :
    (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).heckeRI τ q f)).1 d =
      ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb q.1.1.1.asIdeal q.2 d,
        (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm f).1 e :=
  conj_heckeFamI_apply _ _ (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX) S0 (offSubI.lev q.1, q.2) f d

theorem opEq (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U) (cX : CoefA X.toD7.sp.X') {J : Subgroup (Bridge.Gf X.toD7.sp.X')} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ)
    (hP : ReadsDeco X I hX Xg tr cX t P)
    (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (R : Finset (Bridge.Gf X.toD7.sp.X'))
    (hN : ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ R, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb (q.1.1 : PlI X.B px).1.asIdeal q.2 (decoAd X I t g : Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e)
    (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
    P.ext ((((famR X I hX U Xg tr).heckeRI t q f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
        ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) =
      Bridge.dcOp R (P.ext (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) := by
  obtain ⟨m, hm⟩ := hP
  funext g
  have e1 := hm ((famR X I hX U Xg tr).heckeRI t q f) g
  have e2 := colIn3_heckeRI_apply (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I U)
    Xg ∅ (xiValOf I) tr t q f (decoAd X I t g)
  have e3 := hN _ (fun e => m ((((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 e)) g
  refine e1.trans ?_
  refine (congrArg m e2).trans ?_
  refine (map_sum m _ _).trans ?_
  refine e3.symm.trans ?_
  exact (Finset.sum_congr rfl (fun a _ => hm f (g * a))).symm

theorem chi_eq_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (Q : Pl D.host.E)
    (hQc : Formalism.L2.Col.conjPrime₂ Q = Q) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q) (j : (levEnv V β L).J)
    (hj : IsLocElt V Q (j : Bridge.Gf V)) : (levEnv V β L).χ j = 1 := by
  have e : (levEnv V β L).χ j = Formalism.L2.DIV.levFn β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) := rfl
  have hm : Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L) := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := LiftInertChi.locAt_of_isLocElt V _ _ hj
  have hconj : Formalism.DivisionValues.conjPl Q = Q := GlobalTheory.InertNbr.conjPl_eq_of_conjP hQc
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q →
      Formalism.L2.DIV.redFn β PP (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := fun PP hPP =>
    LiftInertChi.redFn_eq_one_of_locAt _ _ hSt _ hloc PP (fun hu => by
      rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h | h
      · exact hoff PP hPP h
      · exact hoff PP hPP (h.trans hconj))
  have hr1 : Formalism.L2.DIV.rTup β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
    rw [hred PP.1 (Or.inl PP.2)]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  rw [e]
  unfold Formalism.L2.DIV.levFn
  rw [hr1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hPP
    rw [hred PP (Or.inr hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hPP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hred PP (Or.inl hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

theorem gram_eq_one (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem off_level (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px) :
    ∀ PP, PP ∈ (L.datXt t).Pg ∨ PP ∈ (L.datXt t).Q → PP ≠ Q.1 := by
  rintro PP (h | h) rfl
  · have h' : Q.1 ∈ L.Pg := h
    rw [hL.Pg] at h'
    exact Q.2.2.2 (Or.inr h')
  · refine (hL.is.Q_pl t _ h).2 _ h ?_
    exact GlobalTheory.InertNbr.isConjPl_self (D := X.toD7) Q.2.1

theorem inert_neighbours (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hI : I.Ok) (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px)
    (hQ : Q.1 ∉ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (s : List ℕ) (hs : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank s) :
    ∃ (x : Bridge.Gf X.toD7.sp.X') (A : Finset (Bridge.Gf X.toD7.sp.X')), IsLabElt X.toD7.sp.X' Q.1 (labIn X.toD7.sp.X'.rank s) x ∧
      (∀ a ∈ A, IsLocElt X.toD7.sp.X' Q.1 a) ∧ Bridge.IsDC (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J x A ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ A, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb Q.1.asIdeal s (decoAd X I t g : Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e := by
  obtain ⟨m, hm⟩ := hL.is.βX
  rw [one_pow] at hm
  have hβ := hL.beta.2
  rw [hβ] at hm
  have key := GlobalTheory.InertNbr.exists_hecke X.toD7.sp.X' (n := X.B.R.N X.B.R.m - 1) (rank_X' X).symm L.ΛX (L.datXt t) hm Q.1 Q.2.1
    (off_level X I hL t Q) hQ 1 1 (one_mem _)
    (fun x => by
      rw [gram_eq_one X I hI, one_mul, inv_one, mul_one]
      exact (LiftBrg.castGL_mem_UA_one X.toD7.sp.cm (rank_X' X).symm x).symm)
    (one_mem _) (one_mem _) s hs
  simp only [inv_one, one_mul, mul_one] at key
  rw [hβ]
  exact key

theorem exists_inertTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1) := by
  intro X px I hX U Xg tr L eG hI _ hL _ cX gramR c0R _ _ _ _ t P hP
  classical
  have hN := fun (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2) =>
    inert_neighbours X I hI hL t (q.1.1 : PlI X.B px) (fun h => q.1.2 (Or.inr h)) q.2 hq
  exact ⟨{
    hx := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose else 1
    hA := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose_spec.choose else ∅
    hx_ok := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.1
    hA_loc := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.1
    chi_loc := fun q _ j hj => chi_eq_one X.toD7.sp.X' L.βX (L.datXt t) (q.1.1 : PlI X.B px).1 (q.1.1 : PlI X.B px).2.1
      (off_level X I hL t (q.1.1 : PlI X.B px)) j hj
    hDC := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.2.1
    op_eq := fun q hq f => by
      simp only [dif_pos hq]
      exact opEq X I hX U Xg tr t cX P hP q _ (hN q hq).choose_spec.choose_spec.2.2.2 f }⟩

end GlobalTheory.Mem.R3.RowAd.Inert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedRowLatticesFlagLevelRightTranslationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q),
    ∃ u : ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (∀ h : Bridge.Gf X.toD7.sp.X', RowAd.decoAd X I t (h * (q : Bridge.Gf X.toD7.sp.X')) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
          (u : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
            (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
              (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)))))⁻¹) •
          RowAd.decoAd X I t h) ∧
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr u : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  exact @GlobalTheory.Mem.R3.RowDeco.deco_tie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinors
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CanonicalSurjection

theorem canOnto_all : ∀ (D : D7) (Pl : Examples₂.EntPl D), CanOnto Pl := by
  intro D Pl w N nu ν hfit Q hQ M
  haveI : Infinite D.what₂.LL := Infinite.of_injective (Nat.cast : ℕ → D.what₂.LL) Nat.cast_injective
  have h := _root_.GlobalTheory.Mem.WeightBideterminants.weightPolynomial_mem_span_bideterminantProducts D.what₂.LL (Cw D w) (Pl.iL w) D.what₂.Tau N ν M Q hQ
  have e : atBas Pl w M Q = fun y : D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w) =>
      MvPolynomial.eval (fun k : D.what₂.Tau × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2)
        (MvPolynomial.map (Pl.iL w) Q) := rfl
  rw [e]
  refine Submodule.span_le.2 ?_ h
  rintro F ⟨g, hg, rfl⟩
  obtain ⟨J, hJ⟩ := _root_.GlobalTheory.Mem.CanonicalSurjection.prod_bidFns_eq_minY D (Cw D w) N nu ν hfit g hg
  obtain ⟨ph, hph⟩ := _root_.GlobalTheory.Mem.RangeMinors.exists_dual_DeX_eq_minY D (Cw D w) N nu J
  refine ⟨ph, ?_⟩
  funext y
  rw [hJ y]
  exact hph _

end GlobalTheory.Mem.CanonicalSurjection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZeroStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charts_reading_step_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a 0).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad 0 (Nat.zero_le _) (fun c : {c // chOf c = β} => (I.chain l u a).stab 0 c.1) (fun c => latCrd (I.rec7 l Z) 0 (Nat.zero_le _) (I.latAt u a 0 c.1))), I.ReadsK l Z u a 0 (Nat.zero_le _) chOf K := by
  first | exact @GlobalTheory.Mem.Col2.TC.Chart0.charts_zero | exact GlobalTheory.Mem.Col2.TC.Chart0.charts_zero | (intros; apply GlobalTheory.Mem.Col2.TC.Chart0.charts_zero <;> assumption)
end

